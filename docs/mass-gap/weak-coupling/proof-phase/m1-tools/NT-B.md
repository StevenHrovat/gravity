# NT′(b′): few near-cut steps, reduced to a one-step cap lemma (m1-tools, 2026-11-22)

Brief: find a route to part (b′) of Lemma NT′ (`NO-TRAP.md` 4): a pinned core's corrected star has at most `N_cut`
near-cut steps over its whole orbit. Test longer orbits than 31 steps first. Scripts: `nt_b.py` (`run_nt_b.log`),
`cap_fixed.py` (`run_cap_fixed.log`); questions fixed in their headers before running. Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **Long orbits: no near-cut steps at all.** 1500 random stars, labels chosen at the root by the best-cap rule, 300
   steps each: the largest corrected relative angle ever reached was 139 degrees; no step above 160 degrees.
2. **The right invariant is the enclosing cap, not the largest angle.** The largest pairwise angle can grow (by up to 22
   degrees in one step, `NO-TRAP.md` 4), but the radius of the smallest cap containing the corrected star **never grew**
   along any orbit tested, random or adversarial (largest increase found: 0.000 degrees to the solver's accuracy).
3. **Stronger, and a one-step statement:** if all elements of a star lie in a fixed cap `C(u, r)` (all within angle `r` of
   a unit quaternion `u`), every image element of Balaban's star map lies in the **same** cap, strictly inside, for every
   radius tested up to 89 degrees (random stars, stars on the cap's boundary, local search).
4. **The reduction.** NT′(a) (`NT-A.md`) gives, at the root, a label putting the corrected star in a cap of radius
   `arccos s_8 = 84.4°`. If the star map keeps every cap of radius `< 90°` (the **Cap Lemma**), the corrected star stays
   in that cap forever, so all its corrected relative angles stay `≤ 168.7°`: **(b′) holds with `N_cut = 0`** for any
   near-cut threshold below 11.3 degrees from the cut. No dynamics, no capture, no trapping argument is needed; only a
   one-step geometric fact.
5. **Status of the Cap Lemma: open, strongly supported numerically.** In gnomonic coordinates at the reference point the
   cap is convex (a quadric inequality), which proves the analogous statement for the gnomonic barycentre; Balaban's
   average takes the barycentre in logarithmic coordinates, where convexity of the cap's preimage is the open point.

## 1. Tests (`nt_b.py`, `run_nt_b.log`)

| test | result |
|---|---|
| M: measure formula of `NT-A.md` (Monte Carlo, `2·10⁶` points) | agrees to 4 digits at `s = 0.05, 0.0983, 0.2, 0.5` |
| B1: 1500 Haar stars, best-cap label at the root, 300 steps | root cap radius max 69.6° (bound 84.4°); largest corrected angle along the orbits 139.2°; steps above 160°: 0; above 168.7°: 0 |
| B2: enclosing-cap radius along the orbits (first 60 steps; they have contracted long before) | largest one-step increase `+0.000°` |
| adversarial (60 starts, 80 iterations, maximising the cap-radius increase plus the orbit maximum) | largest increase `+0.000°`; orbit maximum 146.1°; steps above 160°: 0 |

Cap radius: `cos r = |p|`, `p` the minimum-norm point of the convex hull of the corrected star (duality: the smallest
cap containing points of an open hemisphere has centre `p/|p|`), computed by accelerated projected gradient on the
simplex.

## 2. The fixed-cap test (`cap_fixed.py`, `run_cap_fixed.log`)

Stars with all elements in `C(u, r)`; largest `angle(t_c, u) - r` over the image elements (negative = strictly inside):

| `r` | uniform in the cap (20000) | on the boundary (20000) | local search (300 starts) |
|---|---|---|---|
| 30° | −7.84° | −3.71° | −7.77° |
| 60° | −15.28° | −4.19° | −8.36° |
| 80° | −11.62° | −1.84° | −3.07° |
| 84.4° | −8.57° | −0.70° | −2.49° |
| 89° | −8.23° | −0.17° | −0.22° |

The margin shrinks as the cap approaches a hemisphere, as it must (for `r = 90°` antipodal pairs on the boundary are
allowed, and there the logarithm's cut is reached).

## 3. The Cap Lemma and what is known about its proof

**Cap Lemma (open).** Let `w_{cb} ≥ 0`, `Σ_b w_{cb} = 1` (Balaban's star weights, `NOTE.md` 2.2, are of this kind). If
`g_1, …, g_n ∈ C(u, r)` with `r < π/2`, then `t_c = exp_{g_c}(Σ_b w_{cb} log_{g_c} g_b) ∈ C(u, r)` for every `c`.

Equivalent form: with `x = g_c`, `a = ⟨x, u⟩ ≥ cos r` and `p` the tangential part of `u` at `x`, the function
`Φ(V) = a cos|V| + (sin|V|/|V|) ⟨V, p⟩` on `T_x S³` (`|V| < π`) has convex superlevel set `{Φ ≥ cos r}` (it is the
preimage of the cap under `exp_x`); the lemma follows because a convex combination of points of a convex set stays in
it, and `0` is in the set.

**What is proved.** In gnomonic coordinates `z ∈ T_x` (`y = (x + z)/|x + z|`, defined for `y` within 90 degrees of
`x`) the cap is `{z : a + ⟨z, p⟩ ≥ cos r · √(1 + |z|²)}`, an affine function above a convex one: a convex set. So the
analogue of the lemma for the gnomonic barycentre holds (for stars within 90 degrees of each reference). That does not
transfer to Balaban's average, which takes the barycentre in logarithmic coordinates `V = θ e` rather than `z = tan θ e`;
and in the regime that matters (corrected root stars, pairwise angles up to 168.7 degrees) elements can be more than 90
degrees from a reference, where gnomonic coordinates do not exist. The numerical margins (section 2) suggest the
superlevel set `{Φ ≥ cos r}` is convex in logarithmic coordinates for all `r < π/2`; a proof would be a curvature
computation of the level set of `Φ` (2-3 pages, plausible, not done).

## 4. Effect

* NT′ is now: (a) **proved** (`NT-A.md`); (b′) **reduced to the Cap Lemma**, a one-step statement about the star map,
  numerically supported with margin; its gnomonic analogue is proved, the logarithmic version is open.
* With the Cap Lemma, the deep-pinned-core part of M1 rests on: P0 (twisted blocking, written), NT′ (a proved, Cap Lemma
  open), P2′ (proof given Balaban's bounds I1-I3), P4 (citation level).
* Small shells: the cap is kept strictly (section 2), so perturbations of size `ε ≪` margin keep the star in a slightly
  larger cap; over the orbit the star contracts (`NO-TRAP.md` 2), so these perturbations do not accumulate. Not written
  out.
