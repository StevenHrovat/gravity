# D-pin scoping: one root per pinned core (m1-tools, 2026-11-22)

Brief: row D-pin of `M1-PLAN.md`, with the owner's accounting rule (`../../PREP.md`, last section, "Deep pinned cores:
one root each"): every pinned core gets exactly one root (its creation scale and site), its suppression is charged
once at the root, and at every coarser scale it is carried as a fixed external defect whose few bonds are not
re-integrated, so the per-step cost should be the local effect of a one-site defect, of order 1. Three checks: (1) is
the core's influence per step bounded independently of the step; (2) is the unique root well defined under Balaban's
region nesting (without grid shifts); (3) does the root suppression summed over roots beat the per-step cost.
Verdict SURVIVES / SURVIVES WITH LEMMA (named) / BREAKS (where).

Sources: `NOTE.md`, `D-N.md`, Balaban [I] (0.4), [IV] (1.2)-(1.9), [V] pp. 363-383 (read earlier), `[15]` Theorem 1.
Three small CPU checks, written before running with their question in the header: `star_dynamics.py`,
`near_vortex.py`, `zlift_traps.py` (each under a minute). Claim marks as in `NOTE.md`. No Lean this round (nothing
elementary here would raise confidence; section 6).

## 0. Result in plain words

1. **Check (2), the root, works (paper).** "Root = the first scale of the current unbroken run of scales at which the
   core's star is deep, and the site at that scale" is a deterministic function of the history, unique, the same for
   every later scale of the run, and needs no grid shifts. Freezing the core and renormalising the rest of its old
   region is still law-preserving: the Lean exactness theorem applies with the frozen data added to the conditioning
   variable. A core that becomes moderate and later deep again gets a new root with a fresh factor (moderate cores
   dilute, Lemma D-mod).
2. **Check (3), the sum over roots, works if the per-step cost is summable, and otherwise is a contest of constants.**
   Pinned cores are deep, so their root suppression is the action itself, `exp(-A_min/g_h²)`, not just Balaban's
   threshold factor `exp(-p0(g_h))`. Asymptotic freedom makes `1/g_h²` grow by about `0.37 log L` (≈ 0.95 for
   `L = 13`) per step of age (one loop, Balaban's normalisation). So: if the per-step carrying cost decays with the
   age (Lemma P2), even the threshold factors suffice; if it is a fixed `C_1` per step, the sum converges iff
   `A_min · 0.37 log L > C_1` (Lemma P3); with threshold factors alone it does not.
3. **Check (1), the per-step influence, is where the risk is.** The frozen core itself is harmless at coarser scales:
   its action is paid once, centre-valued patterns are invisible to the fluctuations (which live in the adjoint), and
   Balaban already shows that an old core reaches the new background only through terms of size `L^{-N}`. That is the
   evidence for Lemma P2. **But** the coarse star of the pinned site reads its whole block, and at a pinned pattern
   Balaban's block average is discontinuous (the logarithm's cut). So the surroundings cannot be renormalised
   analytically right up to the core, which the O(1)-cost carrying needs.
4. **The averaging has to be chosen for this, and the first try fails (numerics).** Under Balaban's own average every
   random deep star at a block centre becomes moderate within about 10 steps, and stars that start near the vortex are
   pushed out in one step: pinning is a knife-edge (a null set). An average made smooth at the vortex patterns instead
   makes them attracting (5% of random deep stars end there) and, in the variant tried, traps a further 33% of deep
   stars elsewhere (not centre-valued; probably at its own discontinuity). Paper argument: for every admissible average, a centre-valued pattern is either a
   discontinuity point or an attracting fixed point.
5. **Verdict: SURVIVES WITH LEMMAS P0 and P2 (P3 as fallback), with P0 the decisive open point.** P0 (averaging design):
   an admissible average, equal to Balaban's near the identity, analytic near every pinned pattern and without trapping
   elsewhere. If no such average exists, pinned cores must be carried as Balaban regions, and the accounting fails as
   in `D-N.md`: that is where it would BREAK. P2 (subscale decoupling): the carried core's effect at `m` steps after its
   root is at most `C L^{-c m}`.

## 1. The rule, precisely

A **pinned core** at scale `m` is a coarse site `y` of the scale-`m` lattice whose star (the `2d` scale-`m` bonds at
`y`) is deep: spread `> r0` (`NOTE.md` 2.3). Its **root** is `(h, z)`: `h` = the smallest scale such that for every
`j ∈ [h, m]` the image of the core at scale `j` is deep (at scale `j` it sits at the star of the coarse site of the
block containing it), and `z` = its site at scale `h`. **Charging:** the root carries the suppression of a deep
scale-`h` large field. **Carrying:** for `j > h`, the scale-`h` core variables (a fixed set of bonds in the scale-`h`
neighbourhood of `z`) are frozen data; the conditional step `R̂` resamples everything else in the old region; the core
is never compared with a small-field reference again.

## 2. Check (1): the influence of a carried core per step

### 2.1 What the frozen core does at coarser scales (paper, partly sketch)

* **Action:** paid once. The frozen core's plaquettes carry the coupling of their own scale (in Balaban's large-field
  regions the coefficient of the Wilson action is position dependent, `(g''_k(·))^{-2} = g_j^{-2}` on scale-`j` shells,
  [IV] p. 187, [V] (1.32)); nothing grows with the age.
* **Background:** the multi-scale background around a frozen hole is Balaban's background with nested domains (`[15]`
  Theorem 1: domains `Ω_0 ⊃ … ⊃ Ω_k`, scale-`j` averages fixed on `Ω_j \ Ω_{j+1}`, shells of width `R M_1` with `R ≥ R_1`
  **fixed**). So the carried object needs shells of fixed width, not Balaban's `M R_j`-cubes (whose polylog size came
  from entropy, not from the variational problem). Balaban's own estimates show the old core enters the new background
  only through H-function terms of size `L^{-N}` ([V] (1.31), (1.47)).
* **Fluctuations:** the frozen bonds are excluded from integration, so at scale `m` the hole is a Dirichlet hole of
  size `L^{-(m-h)}`; in `d = 4` its effect on a Gaussian field scales like its capacity, `L^{-2(m-h)}`. A centre-valued
  pattern (holonomies `±1`) acts trivially in the adjoint representation, in which all fluctuation operators live.

**Lemma P2 (subscale decoupling), open.** The factor by which a frozen root `m` steps old changes the conditional step's
ratio `N/D` at scale `h + m` is `exp(O(1) C L^{-c m})` for some `c > 0`. Balaban's bounds give only `exp(O(B0))` per
step (boundary terms `|B(X)| ≤ B0 e^{-κ d(X)}` for domains touching a large-field region, [III] (2.42)); the three
points above are the evidence that the true size decays.

### 2.2 The obstacle: analyticity at the pinned coarse star

The coarse bonds at `y` average over paths that start at `y` and run through the whole block `B(y)` and into the
neighbouring blocks ([I] (0.3)-(0.4)). So the next field `W` at the pinned star depends on all surroundings within one
block. The conditional step conditions on `W` there and resamples the surroundings in that fibre; the estimates need
that dependence to be analytic (R-terms, [III] (2.31); D1 of `ONE-STEP.md`). At a pinned pattern Balaban's average is
discontinuous: half of the loops are near `-1`, where the principal logarithm jumps. Freezing the whole block-
neighbourhood of `y` instead would cost `O(L^d)` bonds per step (`28561` sites per block for `L = 13`), which check (3)
cannot pay.

### 2.3 Numerical checks (trivial shell, `L = 13`, `d = 4`, 20000 samples each)

| script | question | result |
|---|---|---|
| `star_dynamics.py`, Balaban (0.4) | do random (Haar) deep stars at a block centre stay deep? | no: fraction with spread `> 0.5` is 1.00, 0.99, 0.43, 0.05 after 0-3 steps, 1e-4 after 6, 0 after 12 |
| `near_vortex.py` | stars within `δ` of the vortex pattern | for `δ = 0.01, 1e-4`: all leave the pattern in one step (`δ = 0.1` starts outside the 0.05 window and behaves the same); deep fraction 0.70 / 0.13 / 0.01 / 0 after 2 / 3 / 4 / 6 steps, then trivial. `δ = 1e-8`: 93% stay, a floating-point artefact (`cos` of an angle within `1e-8` of `π` rounds to `-1`, where `log(-1) := 0`) |
| `star_dynamics.py`, "zlift" | an average smooth at centre-valued patterns (relative elements folded into the half-sphere of the reference, sign restored by weighted majority; equal to (0.4) whenever all loops are within `π/2` of the reference, so on the whole small-field regime) | 38% of random deep stars stay deep after 12 steps; 5% sit at centre-valued patterns |
| `zlift_traps.py` | where the remaining trapped stars sit | relative angles spread over `[0, π]` with clusters near 0.1, 1.2, 1.9 and `π` (the 0 bin includes the trivial pairs `b = b'`): not centre-valued; the fold discontinuity is the likely trap (not checked) |

### 2.4 A dichotomy (paper, sketch)

Let `M` be admissible (gauge covariant, conjugation covariant, rotation symmetric, equal to Balaban's average near the
identity), and `s` a centre-valued star pattern reproduced by `M` (`ProofPhase.M1.vortex_persists`). If `M` is
differentiable at `s` with the folded relative elements as coordinates, its derivative there is the linear star map `F`
(central factors pass through), which contracts spreads by `L^{1-d}` (`NOTE.md` 2.2): `s` is attracting, with an open
basin. If `M` is not continuous at `s` (Balaban's (0.4)), `s` is a knife-edge but the surroundings' dependence on `W`
is not analytic there. Either way: with an analytic choice, pinning is generic, which is harmless for the root rule
(each root is charged once); with Balaban's choice, pinning is a null set but cannot be carried at O(1) cost. Any
covariant average on SU(2) has discontinuities somewhere; with near-uniform weights (rows differ by `L^{1-d}`) a
discontinuity can trap stars (the zlift test). Hence:

**Lemma P0 (averaging design), open, decisive.** There is an admissible average, equal to Balaban's (0.4) on the
small-field regime, analytic near every centre-valued star pattern, and such that every deep star at a block centre
reaches either a centre-valued basin or the moderate regime within a bounded number of steps (no trapping at its
discontinuities). Then the pinned objects are exactly the centre-valued patterns, carried analytically at O(1) cost.

## 3. Check (2): the root is well defined (paper)

* **Uniqueness.** For a pinned core at `(m, y)` the run `{j ≤ m : image deep at scale j}` ending at `m` is determined
  by the fields at scales `≤ m`; its first element and the core's site there are the root. Along the run the root does
  not change; a run that is interrupted (the image becomes moderate) ends, and a later deep image starts a new run with
  a new root.
* **Fresh factor for a new run.** If the image is moderate at scale `j` and deep at `j+1`, the deepness is new: by
  Lemma D-mod the old core's contribution is within `θ^{…} r0` of the core-replaced field, so the large plaquette that
  makes the image deep lies outside the old core (the D2 argument of `NOTE.md` 2.3). Each root therefore carries its
  own suppression and no suppression is used twice.
* **Nesting.** The root's old region `Z_h` (Balaban's large-field region) is renormalised by `R̂` once its delay `N`
  has passed, **except** the frozen core. Exactness is unaffected: `map_resample_eq` holds for any conditioning variable
  through which the next blocking factors; take `φ' = (W, V_out, frozen core)`. The frozen core's true density stays
  in the term as a factor.
* **Multiplicity.** A chain at a site `y` of the scale-`k` lattice can be rooted at `y` itself or, at each finer scale,
  at sites close enough to the centre that one step leaves the image deep (path fraction `f(z) π > r0`; `f ≤ 0.36` was
  the maximum for `L = 5, d = 2`, `NOTE.md` 2.3). That is `O(R0^d)` positions per scale, a fixed number.
* **No grid shifts are used.** With a fixed grid, a chain stays at one site per cell.

## 4. Check (3): the sum over roots (paper)

**Root suppression of a pinned core (Lemma P4, citation level).** A pinned core is deep (spread `> r0`). Its weight
carries the Wilson action of a configuration whose scale-`h` plaquette deviates by `r0`: at least `A_min/g_h²` with
`A_min = c0 r0² > 0` (`[15]` Theorem 1 and the mechanism of [V] p. 380, with a one-plaquette domain). This is far
stronger than the threshold factor `exp(-p0(g_h))`.

**Running coupling (one loop, Balaban's normalisation).** [I] (0.2) uses `g^{-2} ∑ (1 - Re tr U)` with `tr 1 = 1`, so
`g_Bal^{-2} = β = 4 g_std^{-2}` for SU(2). With `b0 = 22/(48π²)`, `g_std^{-2}` grows by `2 b0 log L` per step, so
`g_h^{-2} - g_k^{-2} ≈ b (k - h) log L`, `b = 8 b0 = 22/(6π²) ≈ 0.371` (≈ 0.95 per step for `L = 13`). This rests on
[I] Theorem 2 (unpublished proof) and one-loop running.

**(a) With P2 (per-step costs summable to `C_tot`).** Per scale-`k` cell, the roots are `(h, z)`, `h ≤ k`, with `O(R0^d)`
positions per `h`. Even with threshold factors only: `∑_h O(R0^d) e^{C_tot} exp(-p0(g_h))`, with
`p0(g_h) = A0 (log g_h^{-2})^{p0}` and `g_h^{-2} ≥ g_k^{-2} + b (k-h) log L`. The terms decay like
`exp(-A0 p0 (log x)^{p0-1} b j log L / x)` in `j = k - h` (`x = g_k^{-2}`), so the sum is about
`e^{-p0(g_k)} · x/(A0 p0 b log L (log x)^{p0-1})`, and `x = e^{log x} ≤ e^{p0(g_k)/2}`: the total is
`≤ e^{-p0(g_k)/2}` for `g_k` small. **Survives.**

**(b) Without P2 (a fixed cost `C_1` per step).** Threshold factors lose: `p0(g_h)` grows only like `(log(k-h))^{p0}`
in the age while the cost grows like `C_1 (k-h)`. Action-level factors give
`∑_h exp(-A_min/g_h²) e^{C_1 (k-h)} ≤ exp(-A_min/g_k²) ∑_j exp(-(A_min b log L - C_1) j)`, which converges iff

**Lemma P3 (rate condition):** `A_min · b · log L > C_1`, i.e. about `0.95 A_min > C_1` for `L = 13`.

Then the total is `≤ C exp(-A_min/g_k²) ≪ exp(-p0(g_k))`. `A_min` (minimal action of a deep scale-`h` core, in units of
`1/g²`) and `C_1` (Balaban's `B0`-type boundary constant) are not computed anywhere; Balaban's constants are
"sufficiently large/small" without values. Open, a contest of constants.

## 5. Verdict

**SURVIVES WITH LEMMAS**, conditionally:

| lemma | content | status | where it would break |
|---|---|---|---|
| P0 | averaging design: admissible, analytic near centre-valued patterns, no trapping elsewhere | **open, decisive**; Balaban's (0.4) fails it (discontinuous at pinned patterns), the first smooth variant traps 33% (2.3) | if no such average exists: pinned cores need Balaban-region carrying and the accounting fails as in `D-N.md` |
| P2 | subscale decoupling: effect of a root `m` steps old `≤ C L^{-c m}` | open; evidence 2.1 | if false, fall back to P3 |
| P3 | rate condition `A_min b log L > C_1` | open (constants) | only needed without P2 |
| P4 | root suppression of a deep core is `exp(-A_min/g_h²)` | citation level (`[15]` Thm 1, [V] p. 380) | — |
| root bookkeeping | unique root, no double use, exactness with frozen data | **paper, here** (section 3) | — |

So the owner's accounting rule is sound as bookkeeping (check 2) and closes the sum (check 3, given P2 or P3). The open
point has moved from "how to pay for a pinned core" to "how to block-average so that a pinned core can be carried
analytically" (P0).

## 6. Next steps

1. **P0 exploration (cheap, numerical first):** design averages that agree with (0.4) on the small-field regime and
   test them with `star_dynamics.py` for trapping (trivial shell, then random small-field shells). Candidate
   directions: fold relative to the weighted majority cluster instead of the reference bond; a Karcher-type mean on
   SO(3) with a majority lift. A design that passes goes to paper.
2. **P2 on paper:** the subscale-hole estimate (capacity in `d = 4`) and the adjoint triviality of centre-valued
   patterns, against [V] (1.31), (1.47).
3. Lean: nothing elementary worth pinning yet. Once P0 has a candidate, its "no ties at centre-valued patterns" margin
   (weighted majority margin `q S + e1 - e2 s_{-c} s_c ≠ 0`, `S` even; needs `2q > e1 + e2`) is a short Lean lemma.
