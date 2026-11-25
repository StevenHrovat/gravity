# Lemma E7.J: the fibre-mass bound (m1-tools, 2026-11-22)

Brief: prove Lemma E7.J (`E5-E9.md` 2): the blocked Haar measure has density at most `C(L)` per coarse bond, uniformly
in the next block field `W`, handling the logarithm's cut and the fibre's large-field parts. Lean if reachable,
otherwise paper pinned to the sources. Claim marks as in `NOTE.md`. Lean: `formal/ProofPhase/M1/FibreMass.lean`
(`map_prod_le_of_slices`).

## 0. Result in plain words

1. **As first stated (for all fine configurations), E7.J is delicate; with trapping at creation it is a clean
   submersion lemma, proved here on paper.** For arbitrary fine configurations the averaged logarithm can sit near the
   cut, where the exponential map's Jacobian vanishes, and the map from the fine bonds to a coarse bond can degenerate.
   Bounding the density there needs singularity theory (uniform integrability exponents for analytic families). That
   is much more than 3 pages. **But M1 never needs it:** with deep cores trapped **at creation** (delay `N_t = 0`, the
   owner's "one assertion tick") and excised, the fibre integrals of the conditional step only ever integrate variables
   whose plaquettes are below the trapping threshold `r0`. Taking `r0 ≤ c/L²`, all loops of the average are far from
   the cut, and the block map is a uniform submersion with respect to variables that each coarse bond owns.
2. **The bound:** `m_Λ(W) ≤ (C_d L^{3(d-1)})^{|Λ^{(k+1)}|}` for every `W`, where `|Λ^{(k+1)}|` is the number of coarse
   bonds of `Λ` (section 2).
3. **Proof structure:** (a) every coarse bond owns the fine bonds crossing the face between its two blocks (no other
   coarse bond reads them); (b) solve each coarse bond for one owned face bond, away from the trapped holes; its
   derivative is `L^{1-d}` times a matrix within `O(L² r0)` of the identity, so the solution is unique in the small-field
   set and has Jacobian `≥ (L^{1-d}/2)³`; (c) slice: condition on all other variables, bound each slice's pushforward,
   and integrate (Lean: `map_prod_le_of_slices`); (d) the coarse bonds are triangular in their owned bonds, so the
   bounds multiply.
4. **What this changes:** the trapping delay is fixed at `N_t = 0` (trap deep cores at creation). With a positive delay
   the not-yet-trapped deep variables would enter the constraint during those steps, and E7.J would need the hard
   version. The threshold `r0` must satisfy `r0 ≤ c/L²`; the root suppression `exp(-c0 r0²/g_h²)` and Lemma D-mod are
   unaffected (any fixed `r0` works as `g → 0`).

## 1. Statement

**Setting.** The conditional step at scale `k` on a domain `Λ` (union of blocks of the next scale). Integration
variables: the scale-`k` bonds of `Λ` outside the trapped holes, distributed by product Haar measure `dV` (Balaban's
group integrals). Trapped holes: their bonds are frozen and excised (`TRAP.md`); the block map reads their fillings,
which are analytic functions of the surrounding variables (`TRAP-CHECKS.md` T1). After trapping at creation, every term
of the fibre integral restricts the variables by characteristic functions to the set `𝒱_{r0}` where every plaquette of
`Λ` (outside the holes) is within angle `r0` of the identity (any plaquette `≥ r0` would be a deep core, trapped at
creation and excised). `M : V ↦ (Ū(c))_{c ∈ Λ^{(k+1)}}` is the twisted/excised block map.

**Lemma E7.J.** If `r0 ≤ c_d/L²`, then for every `W` the fibre measure `m_Λ(W) = ∫ dV 1_{𝒱_{r0}}(V) δ(M(V) W⁻¹)`
(the density of `M_*(1_{𝒱_{r0}} dV)` with respect to product Haar measure on the coarse bonds of `Λ`) satisfies
`m_Λ(W) ≤ (C_d L^{3(d-1)})^{|Λ^{(k+1)}|}`.

## 2. Proof

**(a) Owned bonds.** For a coarse bond `c = (y, y + L e_μ)`, the fine bonds crossing the face between `B(y)` and
`B(y + L e_μ)` (there are `L^{d-1}`) are read only by the segments of `c` ([I] (0.4): every other coarse bond's paths stay
in its own two blocks and cross only its own face). Fix for each `c` one owned bond `f_c`, not in and not adjacent to a
trapped hole (holes are subscale once carried, `P2-PRIME.md` 1, so all but `O(D0^{d-1})` face bonds qualify) and not the
straight reference path's face bond.

**(b) Small loops.** On `𝒱_{r0}`, in an axial gauge in each block (`[14]`; every bond of a block is a sum over at most
`C_d L²` plaquettes of its axial comb, up to commutator terms of higher order), every bond of the two blocks of `c` is
within `C_d L² r0` of the identity, and so is every loop `P_x U(c)⁻¹` of (0.4) (it bounds a surface of at most
`C_d L²` plaquettes). With `r0 ≤ c_d/L²` all these loops are within `1/2` of the identity: far from the cut, where the
principal logarithm and the exponential are analytic with Jacobians in `[1/2, 2]`.

**(c) The derivative in the owned bond.** `f_c` is used by the segments of the `L` points `x` with transverse
position `x⊥(f_c)`, with total weight `w_c = L · L^{-d} = L^{1-d}` (all `|G|·|G'|` contour pairs of each `x` use it). In
the coordinates `f_c = e^{iX} f_c^0`, `dŪ(c)/dX = w_c (𝟙 + E)` with `‖E‖ ≤ C_d L² r0` (each path's transport depends on
`X` through one factor, conjugated by transports within `C L² r0` of the identity, and the logarithm and exponential
have derivatives within `C L² r0` of the identity there). For `r0 ≤ c_d/L²`, `‖E‖ ≤ 1/2`. Hence on the convex set of
`X` keeping the configuration in `𝒱_{r0}`, the map `X ↦ Ū(c)` is injective (its derivative is within `1/2` of
`w_c 𝟙`), and its Jacobian determinant is at least `(w_c/2)³`.

**(d) One slice.** Fix all variables except the owned bonds `(f_c)_c`. Each `Ū(c)` depends on its own `f_c` and on the
fixed variables only (the fillings do not involve `f_c`: it is not adjacent to a hole). So the map
`(f_c)_c ↦ (Ū(c))_c` is a product of the maps of (c), and the pushforward of Haar measure (restricted to `𝒱_{r0}`)
has density at most `Π_c (2/w_c)³ κ_d` with respect to Haar measure on the coarse bonds, where `κ_d` is the ratio of
Haar densities in exponential coordinates near the identity (bounded). That is `(C_d L^{3(d-1)})^{|Λ^{(k+1)}|}`.

**(e) All slices.** `map_prod_le_of_slices` (Lean): the bound for every slice gives the same bound for the full
pushforward, since the remaining variables carry a probability measure. ∎

## 3. Why the general version is hard, and why it is not needed

Without the restriction to `𝒱_{r0}`, a slice map `f ↦ Σ_j w_j log(a_j f b_j c)` can have critical points (its
derivative is a weighted sum of rotations, which can cancel) and can reach the cut; the pushforward densities are then
unbounded near critical values, though integrable. A uniform bound would combine the many independent face bonds
(convolution of many `L^p` densities is bounded) with a uniform integrability exponent for the analytic family of slice
maps — true by semicontinuity results of singularity theory, but far beyond 3 pages. With trapping at creation, every
deep configuration is excised before it can enter a constraint, so only `𝒱_{r0}` occurs.

## 4. Effect

* Row E7.J: **proved on paper** (given trapping at creation with `r0 ≤ c/L²`); the slicing step in Lean.
* Row E7 and E9: paper, given E7.J (now in hand).
* `TRAP.md`: the delay is `N_t = 0`.

## 5. Comparison with the cut-flag route (owner's reading "the flip is a cut, not a drift")

**The proposal.** Flag a coarse bond when its averaged logarithm reaches angle `π - δ`; send flagged bonds to the
record/large-field branch; restrict the continuous fibre to angles `≤ π - δ`, where the exponential's Jacobian is
`≥ (sin δ/(π - δ))²`; exactness is untouched (`map_resample_eq` holds for any measurable blocking).

**Verdict: the flag route, made complete, is the route of sections 1-2; I keep that one.** Three points.

1. **The cut is only one of two obstructions.** Step 3 of the proposal bounds the density of `Ū(c)` by (density of the
   averaged logarithm `v`) / (Jacobian of `exp`). The second factor is what the flag controls; the first is not
   bounded by the flag. Each owned face bond `f` enters `v` through `L·|G|·|G'|` terms `Σ_j w_j log(a_j f b_j c)` that
   share `f` (section 3), and in a large field the derivative of this map, a positive combination of rotations
   `Ad(a_j)`, can be singular (two terms with `Ad` = identity and a rotation by `π` already give a rank-1 sum). There
   the density of `v` is unbounded, even with `|v|` far from `π`. So the flag must also catch configurations where the
   loops of `c`'s average are far from the identity, i.e. flag `c` when some loop of its average has angle `≥ 1/2`.
   By section 2(b) that happens only if some plaquette of the two blocks of `c` has angle `≥ c_d/L²`.
2. **The flagged branch must not be constrained again.** In Balaban's large-field branch the group integrals are again
   over fibres (that is why E7.J is needed at all, `E5-E9.md` 2). If a flagged bond's coarse value still constrains its
   face bonds, the bound is needed there too, and the argument is circular. So flagged face bonds must leave the
   constraint, i.e. be excised and recorded. That is trapping, with the flag placed on the coarse bond instead of on
   the plaquette, and with threshold `c_d/L²`: exactly `N_t = 0` and `r0 ≤ c/L²` above.
3. **Locality and reflection positivity are fine either way.** The flag of `c` reads the bonds of the two blocks of `c`
   (not only its face: the loops run through both blocks), the same set the average of `c` already reads; the angle is
   invariant under the reflection (`|log h⁻¹| = |log h|`), so `rp_map` applies as for the twisted blocking (`TWIST.md`
   3). Rarity: a flag forces a plaquette `≥ c_d/L² ≫ ε_k = g_k p0(g_k)`, so it is suppressed like a trapped root,
   `exp(-c0 c_d²/(L⁴ g²))` per position, which is `≪ exp(-p0(g))` for any fixed `L` (`TRAP.md` 3).

**Thick vortices (the case asked about).** In SU(2) a vortex of cross-section `A` (fine plaquettes per transverse plane)
spreads its flux `π` over `A` plaquettes, about `π/A` each.
* A vortex about one block thick (`A ~ L²`) puts the loops of a coarse bond's average near `π` with every plaquette
  `~ π/L²`. So **yes: a thick vortex can bring a coarse bond to the cut without any plaquette above a fixed `O(1)`
  threshold** on its face. With flags (or trapping) paid only as deep cores of size `O(1)`, both routes fail exactly
  here. With the threshold `c_d/L²`, the vortex's plaquettes are above it, the bond is flagged / the core trapped, and
  it is paid (still `≫ p0` suppression, point 3). This is why section 1 needs `r0 ≤ c/L²`, not just `r0 = O(1)`.
* A vortex much thicker than a block (`A ≫ L²`) gives loops of size `L` a flux `≈ π L²/A ≪ π`: no flag, no problem at
  this scale. Blocking shrinks its cross-section by `L²` per step; it is caught at the scale where it is about one block
  thick, as above.
* Below threshold nothing drifts to `-1`: on `𝒱_{r0}` with `r0 ≤ c_d/L²`, every coarse plaquette is a fine loop of
  length `4L` bounding at most `C_d L²` plaquettes, so its angle is `≤ C_d L² r0 ≤ 1/2`. **A coarse plaquette near `-1`
  is reached only through a trapped (cut) event, never continuously.** That is the owner's "the flip is a cut, not a
  drift", as a statement of the regime (paper; it is section 2(b) applied to coarse plaquettes).

**Recommendation.** Keep trapping at creation with `r0 ≤ c/L²` (sections 1-2). It is the complete form of the flag
route, it reuses the trapping and excision machinery already checked (T1-T4), and it needs no second record type. The
Z2 labels of the twisted blocking remain an optional refinement for centre-valued cores; they are not needed for E7.J.
