# Milestone 1: the classical thick-vortex background (m1-tools, 2026-11-22)

Brief (coordinator, owner's decision "let's try to finish M1"): the remaining blocker (`F1-REPAIR.md` 4, `ROUTE-B.md` 4)
needs a fluctuation theory around a thick-vortex ("act region") background. Milestone 1 asks for the classical
background: minimisers in the sector with prescribed coarse Z2 flux (existence, shape, action per unit sheet area);
whether the minimum is an act region with a smooth axis field; the Hessian modulo gauge with every zero mode named;
whether it is a genuine minimum with a positive gap off the zero modes; which collective coordinates must be integrated
exactly; how the running coupling fixes the thickness; the literature. Rule: if the milestone shows that the idea
cannot work, stop and report what blocks it. Script: `flux_tube_2d.py` (log `run_flux_tube_2d.log`). Lean:
`formal/ProofPhase/M1/FluxTube.lean`. Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **The background exists, but only with its tile prescribed.** If the set of plaquettes the flux must pass through
   is fixed (a disc of `n` plaquettes in the transverse plane, its boundary holonomy `-1`), the minimum of the action is
   the **uniform abelian flux tube**. All plaquettes have the same angle `π/n` about one axis. Every sub-loop enclosing
   half the flux is an act (`tr = 0`, `U = i n·σ`). So it is an act region with a constant axis, as the owner
   described. Numerically it is the global minimum (12 random descents all reach it). Its action is
   `β n (1 - cos(π/n))`, i.e. `β π²/2 = 2π²/g²` per `T × T` patch of sheet: **scale invariant**. A lower bound with the
   same scaling, `(2/π²) θ²/n` per transverse slice, is machine-checked (`transverse_lower_bound`; the group-theory step
   is on paper).
2. **Without a prescribed tile there is no minimum at finite thickness.** The action per unit sheet area,
   `≈ β π²/(2T²)`, falls as the thickness `T` grows. A straight sheet spreads without limit. A closed sheet spreads
   until it is as thick as it is wide, after which its cost is scale invariant (the dilatation of the whole object).
   On a twisted torus the minimum is a flat twisted connection with zero action, i.e. the flux is completely delocalised
   ('t Hooft). Classically nothing fixes the thickness. Quantum mechanically the running coupling makes thicker vortices
   cheaper still, until `g(T) ~ 1`, which is dimensional transmutation at the confinement scale, **outside M1's
   weak-coupling range** (`k < K`). Inside M1, persistent flux fills whatever cell it is confined to: at the current
   scale its curvature is `O(1)`, the non-perturbative regime of `[15]`.
3. **With only the sign of the coarse flux prescribed, the minimiser sits on the tie.** Requiring `tr hol(∂P) ≤ 0`,
   the cheapest configuration has `tr hol(∂P) = 0`, an act: "the half flip is an act". That configuration lies on the
   boundary between the two Z2 sectors, not inside the flux sector. (Same bound with `θ = π/2`, monotone in `θ`.)
4. **Stability: no negative modes, but one zero mode that is neither gauge nor symmetry.** Hessian of the transverse
   problem (`N × N` box, boundary bonds fixed, `N = 3, 4, 6`):
   * negative eigenvalues: none;
   * zero modes: the `3(N-1)²` gauge modes, plus exactly **two more**;
   * gap above the zero modes: positive, about `8.5-9.6 / N²`.
   
   The two extra modes are one complex **charged** mode (only `σ_1, σ_2` components, i.e. off-diagonal with respect to
   the tube's axis). It is flat to second order and rises as `t⁴`: action change `2.8·10⁻⁷, 4.4·10⁻⁶, 7.1·10⁻⁵,
   1.1·10⁻³` at `t = 0.05, 0.1, 0.2, 0.4` for `N = 3`, the same for `N = 4`. It is the lowest Landau level of the charged
   gluon at exactly zero energy: the borderline of the Nielsen-Olesen instability, since the adjoint flux of a Z2
   vortex is exactly one quantum. It is **not a collective coordinate**: no symmetry moves along it, and the action
   grows quartically. In four dimensions it becomes a massless two-dimensional field on the sheet with a quartic
   self-interaction (sketch: product background, momentum along the sheet adds `p²`).
5. **Verdict on milestone 1: not a genuine non-degenerate minimum.** Two things block the milestone-2 plan (a Gaussian
   `[15]`/`[13]`-type theory with a positive gap once the collective coordinates are split off):
   * **(a)** the quartic charged mode, which a Gaussian theory cannot integrate and which no symmetry lets us integrate
     exactly. Fixing all boundary bonds did not remove it, so Balaban's block constraint (weaker than that) will not
     either.
   * **(b)** the thickness, which is fixed only by the tile (by hand) or by dimensional transmutation (outside M1).
     Inside M1 the background is therefore always at `O(1)` curvature in the units of the current scale.
   
   Per the rules I stop here. Nothing of milestones 2-4 is started.

## 1. The transverse problem

**Setting.** A straight sheet in the `x_3 x_4` directions, flux in the `x_1 x_2` plane through a disc `D` of `n`
plaquettes; holonomy around `∂D` at bi-invariant distance `θ` from 1 (`θ = π` for `-1`, `θ = π/2` for an act).

**Lower bound** (paper for the group step, **Lean** for the inequality). Non-abelian Stokes writes `hol(∂D)` as an
ordered product of conjugated plaquette holonomies. The bi-invariant distance is conjugation invariant and satisfies
the triangle inequality, so `Σ_{p ∈ D} α_p ≥ θ`. Then `Σ_p (1 - cos α_p) ≥ (2/π²) θ²/n` (`transverse_lower_bound`,
from `one_sub_cos_ge`: Jordan's inequality for `sin(x/2)`, and Cauchy-Schwarz). Every transverse slice of the sheet
carries this bound, and the other plaquettes are `≥ 0`. So a sheet of area `A` (in plaquettes) costs at least
`β A (2/π²) θ²/n`.

**Upper bound, attained.** The uniform abelian tube (all `α_p = θ/n`, one axis, the other plaquettes flat) costs
`β A n (1 - cos(θ/n))`, which is `≈ β A θ²/(2n)`. Numerically: `N² S = 4.885, 4.919, 4.932` for `N = 3, 4, 6`, against
`π²/2 = 4.935`. With `n = T²`, the cost per `T × T` patch of sheet is `c_v/g²`, with `c_v = 2π²` (and
`c_v ≥ 8` by the lower bound). This `c_v` enters the rate condition of milestone 3.

**Exact minimality and uniqueness** of the tube: numerical only (descent from 12 random starts at `N = 3`, all reaching
the tube's action to 6 digits). The equality case of the triangle inequality forces all plaquettes to be aligned, and
for `n ≥ 3` (convexity region) the uniform split is optimal. For `n = 2` and `θ = π` it is not unique (`2(1 - cos α)` is
constant along `α_1 + α_2 = π`). Paper sketch, not proved.

## 2. The Hessian

| `N` | dims | zero modes (gauge) | negative | smallest positive × `N²` |
|---|---|---|---|---|
| 3 | 36 | 14 (12) | 0 | 8.46 |
| 4 | 72 | 29 (27) | 0 | 9.19 |
| 6 | 180 | 77 (75) | 0 | 9.61 |

The two non-gauge zero modes: after projecting out the gauge directions, two orthonormal modes remain, entirely in the
`σ_1, σ_2` components (weight 1.000), rising as `t⁴` (table in section 0). Interpretation (sketch): the charged
(off-diagonal) gluon in the field of the tube sees exactly one adjoint flux quantum. Its lowest Landau level then sits
exactly at zero, the borderline between the stable regime and the Nielsen-Olesen tachyon, which appears for larger
flux. The quartic term is the self-interaction of that mode.

**Zero modes, named.**
* **Gauge:** 3 per interior site.
* **Axis:** the global choice of the axis on `S²`. It is gauge when the exterior's gauge is free; fixed when the
  exterior bonds are fixed, as here.
* **Position and thickness:** fixed by the prescribed tile. Without the tile, position is a translation modulus (two
  transverse directions), and thickness is not a modulus but a runaway (the action decreases).
* **Charged mode:** one complex mode, quartic: neither gauge nor symmetry.

## 3. The running coupling and the thickness

Classically: no scale (section 0.2). With the running coupling, a tube of thickness `T` costs `c_v/g²(T)` per `T × T`
patch, and `g(T)` grows with `T`, so thicker is cheaper at every scale where perturbation theory holds. The thickness
settles where `g(T) ~ 1`: dimensional transmutation, the confinement scale. That is beyond M1's stopping scale `K`, where
`g_K ≤ γ` is small. Inside M1 there is no preferred thickness short of the cell size.

## 4. Literature (as recalled; not re-read for this note)

* **Twisted boundary conditions, flux sectors:** 't Hooft, Nucl. Phys. B153 (1979). **Twisted self-dual solutions on
  the torus:** 't Hooft, Commun. Math. Phys. 81 (1981). **Twisted solutions and their stability (tachyonic modes for
  non-self-dual cases):** van Baal (1982-84). **Fractional instantons and vortex-like solutions on twisted tori:**
  García Pérez, González-Arroyo and collaborators (1990s). For a twist in one plane only, flat twisted connections
  exist (anticommuting holonomies `iσ_1, iσ_2`, both acts): zero action, rigid.
* **Instability of chromomagnetic fields:** Nielsen-Olesen, Nucl. Phys. B144 (1978); Ambjørn-Olesen (1988-89).
* **Vortices in pure Yang-Mills are not classical solutions:** Diakonov-Maul (2002) found centre-vortex solutions of
  the one-loop effective action, with thickness set by `Λ`. Bordag (around 2004) studied fluctuations in centre-vortex
  backgrounds and their tachyonic modes.
* **Thick centre-vortex models:** Faber-Greensite-Olejník (1998); random vortex surfaces: Engelhardt-Reinhardt; vortex
  free energy: Kovács-Tomboulis (2000); vortices with a dynamical mass: Cornwall (1979).

The consensus as I recall it: thick centre vortices are quantum objects whose thickness comes from the running
coupling; they are not classical minima.

## 5. What could still be tried (for the owner's decision; not started)

* **Treat the charged mode exactly.** One complex variable per sheet patch with a quartic integral,
  `∫ exp(-β c |w|⁴) d²w ~ β^{-1/2}`, much like the quasi-zero modes of instanton calculus. New, and it couples to the
  sheet's massless 2D field.
* **No fluctuation theory at all.** An extended persistent sheet has a coarse footprint that shrinks by `L²` per step.
  Carried as an ordinary Balaban large-field region, its total carrying cost is dominated by the scale where it is
  born, and is `≈ polylog · g/p0` times its area action, which is small (sketch). Point-like persistent flux becomes
  Route-B labels after the release of its creation-scale large field. This would bypass milestones 2-3, but it is a
  reformulation, so it is the owner's call.
