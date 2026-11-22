# R3, R4: filling next to the cut, swallowed blocks, and the fibre mass (m1-tools, 2026-11-22)

Brief (coordinator, item 2): filling next to the cut with Bianchi-halo data (`r0 = c/L⁴`), the rule for swallowed
blocks, then the fibre mass with the excised bonds filled. Read for this note: `E7J.md`, `TRAP-CHECKS.md` T1, T4,
REVIEW-1 F4. Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **First a correction to the old set-up (F4 was right, and worse than stated).** If the hole is only the set of
   deep plaquettes, the data around it can carry the hole's flux: a loop in the data encircling a deep plaquette has a
   holonomy close to the plaquette's own. Then **every** filling must reproduce that flux, the filled field is deep
   again, and excision gains nothing. The hole has to contain the whole region where the flux sits, so that the data
   around it are **twist-free** (all short loops around the hole near the identity).
2. **The fibre mass is needed only at regular `W`, and there the twist-free hole always exists.**
   * **Where E7.J enters:**
     * at regular `W`, in Balaban's renormalisation of a large-field region (E7, E9: `N_X(W)` for regular `W`);
     * in the existence of fibre densities (X1.H1), which only needs absolute continuity (the block map is analytic
       and generically submersive).
     
     At irregular `W` the region is carried, and Balaban's large-field bounds are integral bounds: intermediate
     δ-integrals integrate to 1, and only the current top scale keeps a δ. So no pointwise fibre mass is needed there.
   * **What regular `W` excludes:** if a flux of class `θ` crosses a coarse plaquette at a pierce point, the fractions
     `f` of averaged loops enclosing it, over the coarse plaquettes around the point, sum to 1. So some coarse plaquette
     has angle `≳ θ/4`. Regular `W` therefore excludes every extended flux with `θ > 4 ε_{k+1}`. Every deep structure in
     the fibre of a regular `W` is **localised**, closed within a ball of radius `≤ C L`, and twist-free outside.
3. **The filling (R3), paper.**
   * **The hole:** the twist-free envelope of the deep plaquettes, built deterministically. Grow the hole by layers
     until every loop of length `≤ 8` around it has holonomy `≤ C r0`, with a cap at radius `C L`; if the cap is
     reached, there is no excision and the configuration lies in an irregular-`W` fibre.
   * **The filling:** the least-action configuration on the hole given the twist-free data on its outer boundary. This
     is a small-field Dirichlet problem: the data are within `C r0 L²` of a pure gauge on the hole's neighbourhood, so
     the filling is unique modulo gauge, analytic in the data, and regular, with filled plaquettes `≤ C r0 L²`.
   * **No per-block restriction any more.** Per-block filling was only needed for reflection positivity, which is
     dropped (`M1-PLAN.md` 0). So **swallowed blocks** (a hole covering whole blocks) are filled together with the rest
     of the hole from its outer boundary.
   * **Measurability:** the envelope is a finite deterministic growth with fixed thresholds, so it is measurable. The
     thresholds sit at loop holonomies `C r0`, inside the small-field regime, not at the cut.
4. **The fibre mass (R4), paper with one compactness step.**
   * **Ordinary coarse bonds:** as in `E7J.md` 2: owned face bonds away from holes, derivative `w_c(1 + E)` with
     `‖E‖ ≤ C L² r0 ≤ 1/2` (all loops of the average now pass through regular or filled field within `C L² r0`), and
     slicing (`map_prod_le_of_slices`, Lean).
   * **Swallowed coarse bonds** (a hole covering a coarse bond's whole face): the coarse value is a function of the
     hole's outer data through the filling. Use as owned variables the outer-boundary data bonds of the hole nearest
     to that face. The map from them to the swallowed coarse values is, to leading order, a fixed linear map (averaged
     harmonic measures) that depends only on the hole's shape and the block geometry. For `L` fixed there are finitely
     many shapes of radius `≤ C L`, so its smallest singular value has a positive lower bound `s(L) > 0`, if each map is
     surjective, which holds because boundary data near each face move that face's filled bonds independently. **The
     surjectivity and the compactness bound are a sketch.** This gives a fibre-mass constant `C(L)` per swallowed bond,
     not explicit.
5. **Status:** R3 paper; R4 paper for ordinary bonds (as E7.J) and sketch for swallowed bonds (surjectivity plus
   compactness, constant not explicit). It does not fail, but the swallowed-bond Jacobian is the weakest point.

## 1. Why the old hole is wrong

A single deep plaquette `p` (angle `θ ≥ r0`) whose hole is its 4 bonds: the boundary of the `3 × 3` square around `p`
uses only data bonds, and its holonomy is the ordered product of the 9 plaquettes inside, about `θ`. Any filling of the
4 hole bonds must therefore put a flux of about `θ` into the plaquettes containing them: at least `θ/21` per plaquette,
still `≫ r0` when `θ = O(1)`. Excising only the deep plaquettes cannot regularise a flux-carrying core.

## 2. The twist-free envelope

* `H_0` = bonds of plaquettes at angle `≥ r0`.
* `H_{i+1} = H_i ∪` (bonds within distance 1 of `H_i`), as long as some loop of length `≤ 8` in the complement that
  encircles a plaquette of `H_i` has holonomy `> C r0`.
* Stop when there is none (twist-free) or at radius `C L` (then: no excision).

For a localised core (gauge representative supported in a ball `B_ρ`), the growth stops by radius `ρ + 1`: outside the
ball every short loop sees only the regular field. For an extended flux the cap is reached, and by section 0.2 that
configuration is not in the fibre of a regular `W`.

## 3. The filling as a small-field problem

On the envelope's neighbourhood `N`, the data are twist-free: all short loops are within `C r0`, so in an axial gauge on
`N ∖ H` the data bonds are within `C r0 · diam(N)` of the identity, which is `≤ C r0 L ≤ C c L^{-3}`. Minimising the
Wilson action of the plaquettes meeting `H` over the bonds of `H`, with these data, is a Dirichlet problem near the
identity. Its Hessian is the Dirichlet Laplacian of `N` (positive, gap `≥ c/diam(N)²`), so for data `≤ c/diam(N)²` the
minimiser is unique, analytic and within `C r0 L²` of the identity in plaquettes (implicit function theorem; the same
estimate as `TRAP-CHECKS.md` T1, now with twist-free data). With `r0 = c/L⁴` the data bound `C c L^{-3}` is below
`c'/L²` for small `c`.

## 4. Effect

* F4 (REVIEW-1): closed in this form.
* `E7J.md` holds at regular `W` with holes = twist-free envelopes; the "trapping at creation" set-up of `E7J.md` 1 is
  replaced by this excision rule.
* In `M1-PLAN.md`: R3 **paper**; R4 **paper** (ordinary bonds) + **sketch** (swallowed bonds).

**Update (REVIEW-2 G6, N3):** the growth cap is on the number of layers, not the extent; extended thin slabs (centre-flux sheets) are filled in local gauges with the Dirichlet gap `(π/w)²` (`REVIEW2-RESPONSE.md` 3). "Unique modulo gauge" is made measurable by an axial gauge selection in each patch, rooted away from block centres where Balaban's average is covariant.

**Update (REVIEW-3 H5; `REVIEW3-RESPONSE.md` 2):**
* The twist-free test with loops of length `≤ 8` was vacuous. It uses loops of length up to `λ = 8(ℓ_max + 2)` in the
  first outer layer, with threshold `C_tw r0 |γ|²`.
* Cap: `ℓ_max = C_1 L ≥ C L + 1`.
* The filling is the implicit-function critical point, not "the least-action configuration".
* Owned bonds lie outside the Dirichlet data.
* "Cap reached implies irregular `W`" remains a sketch, through section 0.2.
* Sections 0.4-0.5 (surjectivity and compactness for swallowed bonds) are superseded by the randomised swallowed bonds
  (`SKETCH-STEPS.md` 1).

**Update (REVIEW-3 follow-up NIT 2; `REVIEW3-RESPONSE.md` 11.7):** with the new test threshold, the data deviate from pure gauge by up to `C_tw r0 λ² ≈ 64 C_tw C_1² c L^{−2}`, not `C c L^{−3}`. The filling closes for `c ≤ c'/(256 C_tw C_1^4)`, with `c` chosen after `C_1` and `C_tw` (`S1-INDUCTION.md` 1).

**Update (`UV-TV.md` 35.1):** the twist-free test uses the uniform threshold `C_tw r0 λ²` for every loop of length `≤ λ` in `O(H)`, with `C_tw ≥ 8 max(C, 1)`. With it, "cap reached implies irregular `W`" is proved at paper level by coarse non-abelian Stokes (an exact inequality) and the gauge covariance of Balaban's average. The "fractions sum to 1" step of section 0.2 is no longer needed.

**Update (`UV-TV.md` 38.2, after REVIEW-2 and REVIEW-3 on 35.1):**
* Holes grow per cluster of `H_0`, the components under `dist ≤ D = 2ℓ_max + 2`: `H_C^{(i)} = N_i(C)`. So holes of different clusters never touch, and at the cap `O(H_C)` is at distance `≥ ℓ_max + 1` from all of `H_0`.
* "Cap reached implies irregular `W`" is proved for any failing loop. It joins the loop to its coarse shadow through a ribbon of width `O(L)` avoiding `H_0`, then uses coarse Stokes, with `C_1 ≥ C_3` and `C_tw ≥ (C_6 + C_7)/4`.
* The twist-free test and the filling are unchanged. The previous update's claim (closure via 35.1) is replaced by 38.2.
