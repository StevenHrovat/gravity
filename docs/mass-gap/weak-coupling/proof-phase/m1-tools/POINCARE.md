# The Poincaré bound for the block-axial gauge (m1-tools, 2026-11-22)

Brief: the Poincaré step of E3 (`E3.md`, Balaban's [V] (1.8)) for the gauge and constraints of the conditional step:
fluctuations on the scale-`k` bonds of `Λ` that vanish on a spanning tree of every block (block-axial gauge), have zero
linearised block averages on every coarse bond reading `Λ`, and vanish outside `Λ`. Claim marks as in `NOTE.md`. Lean:
`formal/ProofPhase/M1/FibreMass.lean` (`sum_sq_le_of_paths`, the counting step).

## 0. Result

**Lemma (Poincaré, block-axial).** Under these conditions
`Σ_{b ∈ Λ} |B'(b)|² ≤ C d⁴ L^{2d+2} Σ_{p} |∂B'(p)|²`,
the sum over plaquettes touching `Λ`. (Balaban's (1.8) has `d (100M)^{d+1}` for a single axial tree in a region of side
`100M`; the block-axial constant depends only on `L`.) **Status:** proved on paper (section 1) at the linearised level
(the covariant version on a small-field background is the same argument with parallel transports within `O(ε)` of the
identity, as in Balaban's); the counting step is machine-checked (`sum_sq_le_of_paths`: if every bond value is bounded by
a sum of `|∂B'|` over a set of at most `s` plaquettes and every plaquette is in at most `t` such sets, then
`Σ |B'|² ≤ s t Σ |∂B'|²`).

## 1. Proof

Blocks `B` of side `L` (odd) centred at the coarse sites; in each block the axial tree `T_B` from the centre (first along
`e_1`, then `e_2`, …). `B' = 0` on every `T_B` and outside `Λ`.

**(i) Bonds inside a block.** For `b = (x, x + e) ⊂ B`, `b ∉ T_B`: the tree paths from the centre to `x` and to `x + e`,
with `b`, form a closed loop of length `≤ dL + 1`; for an axial tree it bounds a "staircase" surface `S_b` of at most
`d L²` plaquettes inside `B`. Discrete Stokes (`B'` vanishes on the tree): `B'(b) = Σ_{p ∈ S_b} ± ∂B'(p)`, so
`|B'(b)| ≤ Σ_{p ∈ S_b} |∂B'(p)|`, `|S_b| ≤ d L²`.

**(ii) Bonds crossing a face.** For the coarse bond `c` between `B` and `B'` with face bonds `f_{x⊥}` (`x⊥` the
transverse position): every path of (0.4) is `Γ` in `B`, then a segment (interior bonds of `B`, one face bond, interior
bonds of `B'`), then `Γ'` in `B'`. Along any path inside a block from its centre, `B'` equals its value along the tree
path to the same end point plus a surface term of at most `d L²` plaquettes, i.e. a surface term. So the linearised
constraint `Q B'(c) = Σ_{x⊥} W_{x⊥} B'(f_{x⊥}) + (surface terms) = 0`, with `Σ W_{x⊥} = 1`: the weighted mean of the
face values is a weighted average (weights summing to 1) of surface terms inside `B ∪ B'`, so its absolute value is at
most `Σ |∂B'(p)|` over all plaquettes of `B ∪ B'` (at most `C d L^d` of them). Neighbouring
face bonds differ by one face plaquette and two interior bonds: `B'(f_{x⊥}) - B'(f_{x⊥ + e}) = ∂B'(p) + (two interior
values)`, each interior value a surface term of `≤ d L²` plaquettes. Walking from any face bond to the weighted mean
along at most `(d-1)L` face steps (each adding one face plaquette and two surfaces of `≤ d L²` plaquettes inside
`B ∪ B'`): `|B'(f)| ≤ m Σ` over a set of at most `C d L^d` plaquettes (all of `B ∪ B'` and its face), where
`m ≤ 2(d-1)L + 1` bounds how often one plaquette is reused along the walk. Coarse bonds crossing `∂Λ`
are treated the same way with the outside block's values zero.

**(iii) Counting.** `s = C d L^d` (the face sets; interior sets have `≤ d L²`). A plaquette lies in the sets of the
interior bonds of its block (at most `d L^d`) and of the face bonds of the faces of its block and its neighbours (at most
`2d · 2d · L^{d-1}`): `t ≤ C d L^d`. Applying `sum_sq_le_of_paths` to `B'/m` (so that the multiplicities are absorbed):
`Σ |B'|² ≤ m² s t Σ |∂B'|² ≤ C d⁴ L^{2d+2} Σ |∂B'|²`. ∎

## 2. Effect

`E3.md` row (1.8): done (paper + Lean counting step), constant `C d⁴ L^{2d+2}` (for `L = 13`, `d = 4`: `L^{10} ≈ 1.4·10^{11}`
times a constant; comparable to or smaller than Balaban's `d (100 M)^{d+1}` for `M ≥ L`; the crude counting is not
optimised, and only the `L`-dependence, not `g`-dependence, matters). E3 and E7 no longer have an open sub-step.
