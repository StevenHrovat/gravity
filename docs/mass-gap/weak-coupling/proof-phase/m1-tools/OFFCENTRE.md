# R1: dilution of localised moderate cores at every position (m1-tools, 2026-11-22)

Brief (coordinator, item 1 of the open list in `M1-PLAN.md` 0): prove the contraction of localised moderate cores
away from block centres (F5), in SO(3), including sub-block sheet cores; Lean if reachable. Read for this note: [I]
(0.3)-(0.4) (the average), `NOTE.md` 2.2-2.3 (the centre case), `ROUTINE-ROWS.md` 4 (BCH constants). Script:
`offcentre_cancel.py` (log `run_offcentre_cancel.log`). Lean: `formal/ProofPhase/M1/OffCentre.lean`. Claim marks as
in `NOTE.md`.

## 0. Result in plain words

1. **R1 is proved on paper, for every position at once, and the centre is not special.** The proof rests on one
   structural fact of Balaban's average (0.4). A coarse bond `c` at the coarse site `y` averages loops made of a
   shortest path `Γ` inside the block `B(y)`, a straight segment, a return path `Γ'` in the neighbouring block, and the
   reference. The law of the `B(y)`-part (end point uniform in `B(y)`, order of directions uniform) is **the same for
   every coarse bond at `y`**, incoming or outgoing. So, to first order, the `B(y)`-part of a perturbation is a coarse
   gauge transformation at `y` and drops out of every coarse loop. **Only the straight segments transmit a localised
   perturbation.** Each fine bond lies on at most `L` of a coarse bond's segments, each of weight `L^{-d}`, so a coarse
   bond moves by at most `L^{1-d} Σ_{b ∈ S} |a_b|`, where the sum runs over the perturbed bonds in its own direction.
2. **The lemma.** Let a perturbation `a` of an `ε`-regular background be supported in the stars of the sites of a ball
   of radius 2 (sup distance; at most `5^d` sites), with `|a| ≤ r0`. Then the blocked perturbation is a coarse gauge
   transformation plus a perturbation of the same kind at the next scale (supported in the stars of the coarse sites of
   the blocks met, again a ball of radius `≤ 2`), with
   `M' ≤ θ M`, `θ = 5^d L^{1-d} + C_d (r0 + L² ε)`,
   where `M` is the smallest `max_b |a_b|` over gauge-equivalent representatives. For `d = 4`, `L = 13`:
   `5⁴/13³ = 0.284`, and the correction is negligible for `r0 = c/L⁴`. A star (one site) gives `2·2^d L^{1-d}`, and
   numerically at `L = 3` the worst coarse plaquette change over all positions is `0.088 max|a|`, under the proven
   `4 L^{1-d} = 0.148`. In that test exactly the 8 coarse bonds at the block's own coarse site moved, as the proof says.
3. **Iteration:** `M_{k+n} ≤ θ^n M_k`. The plaquettes of the perturbed field are within `4M` of the background's, so a
   core is regular after `n ≥ log(8 M_k/ε)/log(1/θ)` steps, `O(log g^{-2}/log L)`. A first step from any larger ball
   (radius `R ≤ L`) lands in the class with factor `(2R+1)^d L^{1-d}`.
4. **SO(3):** the same, word for word. Everything is linear in the Lie algebra (`so(3) ≅ su(2)`) plus BCH bounds in an
   `Ad`-invariant norm, and moderate cores are far from the SO(3) cut.
5. **Sub-block sheet cores are not diluted by this mechanism, and do not need to be.** An extended slab is not a
   bounded support (the segment count grows with its area), and its SO(3) content inside the slab is deep (rotations up
   to `π`). In SO(3), however, a thin Z2 sheet carries no twist (`Ad(-1) = 1`), so the one-step excision and filling of
   the main line (R3) replaces it by a smooth field. Moderate extended sheets grow to deep (thick phase) and are excised
   then. So sheets belong to R2/R3, not to R1. Stated plainly: R1 covers bounded supports only.
6. **Lean:** the two elementary steps, `wavg_common_cancel` (common parts cancel in a difference of weighted means)
   and `sum_abs_sum_le_mult` (few segments per bond).

## 1. The structure of (0.4)

For a coarse bond `c = (y, y + L e_μ)`, (0.4) averages, with weight `L^{-d} |G|^{-1} |G'|^{-1}`, the logarithms of the
loops `Γ ∪ [x, x + L e_μ] ∪ (-Γ') ∪ (-c)`, over `x ∈ B(y)`, `Γ ∈ G(y, x)`, `Γ' ∈ G(y + L e_μ, x + L e_μ)`. For an
**outgoing** bond the `B(y)`-part is `Γ`: `x` uniform in `B(y)`, `Γ` uniform in `G(y, x)`. For an **incoming** bond
`(y - L e_μ, y)` the `B(y)`-part is `Γ'`: its end point `x + L e_μ` is uniform in `B(y)` and `Γ'` is uniform in
`G(y, ·)`, traversed backwards. **Same law, opposite orientation.** That is exactly how a gauge transformation at `y`
acts on outgoing and incoming bonds.

**Linearisation.** With `V' = e^{ia} V`, the first-order change of a loop's logarithm, based at `c_−`, is
`Σ_{b ∈ S ∩ loop} ± Ad(T_{c_− → b}) a_b`. The reference `c` (straight path) cancels at first order (`NOTE.md` 2.2).
Split by where `b` lies:
* **(i)** on `Γ`: the average is `X(c_−) := E[Σ_{b ∈ S ∩ Γ} Ad(T_{y→b}) a_b]`, a function of the site `c_−` alone;
* **(ii)** on `Γ'`: `-Ad(Ū(c)) X(c_+)` up to `O(L² ε)|a|`. The transport from `c_−` through the loop to `b` is the
  coarse transport times the loop's background holonomy, which is `1 + O(L² ε)`;
* **(iii)** on the segment: the remainder `R_c`.

So `δŪ(c) Ū(c)^{-1} = X(c_−) - Ad(Ū(c)) X(c_+) + R_c + O(L² ε)|a|`. The first two terms are the coarse gauge
transformation `u(y) = X(y)` (**Lean** step: `wavg_common_cancel`).

**Segments.** A bond `b` in direction `μ` lies on the segments of `(y, y + L e_μ)` started from at most `L` points of
its line, each with total weight `L^{-d}`. Hence `|R_c| ≤ L^{1-d} Σ_{b ∈ S, dir μ} |a_b|` (**Lean** step:
`sum_abs_sum_le_mult` with `t = L`). In a ball of radius `R`, at most `(2R+1)^{d-1}` lines in direction `μ` meet `S`,
each in at most `2R + 1` bonds, which gives the factor `(2R+1)^d`.

**Support.** Loops avoiding `S` are unchanged, so only coarse bonds whose loops meet `S` move: those at the coarse sites
of the blocks meeting `S`. A ball of radius `R ≤ L` meets at most `2^d` blocks with adjacent centres, so the image lies
in the stars of the vertices of a coarse unit cube, a ball of radius `1 ≤ 2`. The class is invariant.

## 2. Nonlinear corrections

As in `ROUTINE-ROWS.md` 4: per loop, the derivative of `log` deviates from the identity by at most
`0.51(|Z| + |a|)` (`ad` skew, `|f(it) - 1| ≤ 0.51 t`). Here `|Z| ≤ 2 |S| r0 + d L² ε`: a loop passes the support at most
`|S|` times, and its background part bounds `≤ d L²` plaquettes. The common-part cancellation holds exactly for the
linear terms; the nonlinear terms add at most `C_d (r0 + L² ε) max|a|` per coarse bond. The mean-value inequality along
the segment `t a`, `t ∈ [0, 1]`, gives the stated `θ`.

## 3. Numerical check (`run_offcentre_cancel.log`)

`d = 4`, `L = 3`, trivial background, a random perturbation of size `10⁻⁴` on the star of `x`, for every offset class
of `x` in its block. Per offset: `(max coarse plaquette angle)/max|a|` = `0.054` (centre), `0.086, 0.079, 0.088, 0.086`
(off-centre); bound `4 L^{1-d} = 0.148`. In every case exactly 8 coarse bonds moved: the star of the block's own coarse
site.

## 4. What this does and does not cover

* **Covers:** every localised moderate core (bounded support, `|a| ≤ r0`) at every position, in SU(2) and SO(3); this
  replaces the numerical off-centre step of `NOTE.md` 2.3 (F5) and unifies it with the centre case.
* **Does not cover:**
  * extended moderate structures (they grow to deep: R2);
  * deep cores and sub-block sheets (excised and filled: R3).
