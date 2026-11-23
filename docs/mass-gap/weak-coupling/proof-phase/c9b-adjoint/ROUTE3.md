# Route 3 for the IR side: the column in the dichotomy frame, and the small-box measurement (c9b, 2026-11-23)

Owner, relayed: "Please ... turn the IR session to the new route" and "For the IR stuff: The finer resolution and smaller size approach goes
toward the one-box model everything is based on, so I think that is a good direction to head towards for a most efficient way to get the
answers we need out of it." Inputs: `../c9a-crossover/DICHOTOMY.md` (sections 4, 8; (D″)), `REDESIGN.md` (sections 3, 8), `TIMING.md`
(the 40^4 timing result), `PILOT2.md`. Marks: **Lean**, **paper**, **numerical**, **sketch**, **open**. Nothing here was run on the GPU.
The CPU numbers are seconds-scale quadrature (`krd_derive.py`-type, inline in this note's section 4).

## 0. Results in plain words

1. **The W1 column splits exactly as the dichotomy does** (paper, exact split).
   - The **inside part** is the partners whose cells lie within one cell of `x`'s cell: plaquette, rectangle and bent-loop partners. No
     full cell separates them from `x`.
   - The **tail** is the partners with at least one full cell between, which play the role of a collar. Behind a collar the influence
     is a boundary term attenuated like `e^{-m L1 (d - 1)}`, given **condition A** (a conditional mass `m > 0` in the collar). The
     inside part is the dichotomy's residue: crossing flux, near-cut percolation, and the direct coupling.
2. **The combination is Lean-ready**: `Adjoint2/Transfer.lean`, `residual_budget` with `m_fit -> m_in`, `m_res -> m_tail`. The column is
   `< 1` once the inside and tail mixed-variation columns sum to `< log 3`. Nothing new to prove for the combination.
3. **The tail bound is solid only far out** (paper, crude). Lemma C's prefactor counts fine interface sites, about
   `(b^3)^2 = 2.6 x 10^5` at `b = 8`, and the partner count grows like `(2d + 1)^4`. A block-constrained fluctuation field has a
   conditional mass of order the inverse block size (Poincare in scale units; recalled from Balaban and M1's Lemma UV-TV):
   `m L1 ~ 2 pi`. Per-shell terms `(2d + 1)^4 x 2.6 x 10^5 x e^{-m L1 (d - 1)}`:
   - at `m L1 = 2 pi`: 3 x 10^5, 2 x 10^3, 11, 0.05 for `d = 2, 3, 4, 5`;
   - at `m L1 = 12`: 10^3, 0.02, 4 x 10^-7 for `d = 2, 3, 4`.

   **So the analytic leg bounds only the tail from `d >= 5` cells (`d >= 3` if `m L1 >= 12`)**, which is small but was never the
   problem. Everything nearer joins the inside part. Condition A is open (DICHOTOMY 8.6).
4. **The inside part is where the gap-strength input lives, and it is not small at `L1` for `beta = 2.3`.** The crossover session measured
   near-cut percolation spanning the box in 100 % of sampled boxes at `beta = 2.3` (`DICHOTOMY.md` 8.6). The fitted action's inside
   column (plaquette 0.73 plus rectangle 0.23, W1) is already 0.96 of the 1.
5. **The small-box measurement measures exactly the inside part**, at the smallest size where it is defined: a periodic coarse 3^4 torus
   (fine 24^4 at `b = 8`), every coarse link except `x` pinned. By the provability rule it can **only refute** (section 3). The fitted
   action predicts **no refutation**: the measurable lower-bound column is about 0.4-0.65.
6. **Projection** (section 4, `PROJECTION.md` section 8's rule): the cheapest informative variant (`b = 4` near `beta = 2.15`, 12^4, the
   antipodal flip of the ss class to +-30 %, one background) costs **about 20 GPU-hours central (band 14-36 h)**; a minimal decisive set
   (5 backgrounds, the ss class, two `kappa_c`) about **200 h central (135-355 h)**. The W1-move version is 20 times more.
   **Recommendation: no GPU run for the small box in this form.** Its only possible outcome of value (a refutation) is predicted not to
   occur, and a PASS cannot discharge anything.

## 1. The split (paper; exact as a decomposition)

For the coarse conditional specification at `L1` (sites = coarse links; `H(v_x | rest)` the true conditional log-density, rest = all
other coarse data and the fine outside), and the mixed variation `Mix_xz` of `REDESIGN.md` / `NOTE.md` 1.3:
- **Inside set** `N_in(x)`: partners `z` at cell distance `d <= d_0`, with plaquette (18), rectangle (90) and bent-loop partners at
  `d <= 2`, where no full cell separates `z` from `x`. `d_0` is where the tail bound of section 2 becomes small: `d_0 = 4` at
  `m L1 = 2 pi`, `d_0 = 2` at `m L1 = 12`.
- **Tail** `N_tail(x)`: `d > d_0`. Between `z` and `x` lie at least `d - 1` full cells, which serve as a collar.

`Mix_xz` for `z` in the tail is a cross term mediated by the fine field in the collar. By the Markov property of the finite-range
specification (exact) it enters only through the collar's layers. By Lemma C's inequality (`WL.md` 6.2, paper) it is at most
`C_A |d_x||d_z| e^{-m L1 (d - 1)}`, with `|d_x|`, `|d_z|` the fine interface sizes (about `b^3` each), **given condition A**.

**The combination (Lean, existing).** `Transfer.lean`: `column_lt_one_of_mix` (pair coefficients `<= (e^{m_z} - 1)/2`, `sum m < log 3`
gives column `< 1`) and `residual_budget` (`m <= m_fit + m_res`, `sum m_fit + sum m_res < log 3` gives column `< 1`). Applied with
`m_fit := Mix_in` (the inside pairs, zero off `N_in`) and `m_res := Mix_tail` (zero on `N_in`): **the column is `< 1` once
`sum_{N_in} Mix + sum_{tail} Mix < log 3`**. The sharp form (`tanh(Mix/4)` per pair, `NOTE.md` 2(a)) allows more. No new Lean is
needed; the inputs are the two sums.

## 2. What the analytic leg can bound, and what it cannot

**The tail** (paper given condition A; crude constants). `sum_d N(d) C_A b^6 e^{-m L1 (d - 1)}` with `N(d) <= c (2d + 1)^4` partners
at cell distance `d`. Shell terms over `c C_A`:

| `m L1` | `d = 2` | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|
| `2 pi` (the block-constrained Poincare mass, recalled) | 3.0 x 10^5 | 2.2 x 10^3 | 11 | 0.05 | 2 x 10^-4 |
| 12 | 10^3 | 0.02 | 4 x 10^-7 | | |

So the tail is small only from `d = 5` on at `m L1 = 2 pi`, and from `d = 3` on at `m L1 = 12`. Its reach is set by `m L1`, which is
open (condition A). **The inside part is therefore cell distance `<= 4` (`<= 2` if `m L1 >= 12`), not just the plaquette and
rectangle shells.** (Correction made before reporting: a first version of this paragraph had the `d = 3` term as about `2 c C_A`, an
arithmetic slip; it is 2.2 x 10^3.)

**The inside part cannot be bounded analytically at `L1`** (paper; it is the residue). No small parameter: the coarse variables are near
Haar (c4d), the near-cut set percolates inside the box at `beta = 2.3` (DICHOTOMY 8.6), and crossing flux is unscreened (Lean,
`cob_restrict_eq_cob_restrict_compl`). Its smallness is the gap-strength input. The fit-side value is 0.96 of the W1 column (c4d,
ext_R), all of it inside.

**Lean status for this leg.** The combination is Lean (`residual_budget`). The tail's geometric sum is a routine series bound (not done:
it adds nothing until `m L1` is known). Lemma C at the cell scale and condition A are open (as in `ROUND2.md` 2.3 (b)).

## 3. The small-box measurement: what it measures, and what it can prove

**The object.** A periodic fine lattice of 3 cells per side (24^4 at `b = 8`; 12^4 at `b = 4`): the coarse torus 3^4. Every coarse link
except `x` is pinned by the penalty, `kappa_c -> infinity` by extrapolation, and the fine field is integrated everywhere (no frozen fine
outside).

**How it changes the measured conditional law** (against the planned radius-2 region on 40^4):
- (i) **Conditioning:** `p(v_x | all other coarse links of a 3^4 torus)` instead of `p(v_x | the coarse links within distance 2,
  fine outside frozen beyond)`. The small box conditions on every coarse link of the system and on no fine data. It is the exact
  finite-volume coarse specification of a 3^4 coarse torus, which is cleaner than the frozen-outside version.
- (ii) **Finite volume:** partners at distance 2 and 1 coincide around the torus at side 3 (a 1x2 rectangle wraps). So the measured
  rectangle-class coefficient mixes two partner classes. The plaquette class is clean (side 3 keeps `x +- nu` distinct).
- (iii) **Wrap-around:** the infinite-volume specification differs by terms behind at least one full cell, the tail of section 2,
  attenuated given condition A (crude: not small at `d = 2`, see above).

**Provability (REDESIGN.md section 8 rule).**
- What the box measures, for a pair `(x, z)` and a background `beta_0`: `TV_meas(x, z; beta_0)` (or `KR_meas`). This is the change of
  `p(v_x | ...)` under one move of `V_z` at the tested coarse configuration.
- The Lean coefficients are suprema. `Mixing/Classical.lean`: `dob x z` is the max over configurations differing only at `z`;
  `Certified/AdjointW.lean`: `SiteInfluenceW`'s `k i z` holds for **every** boundary and value. So
  **`TV_meas <= dob(x, z)` and `KR_meas/delta <= Lip_xz`** (a supremum dominates any instance; for a flip, chord <= Lipschitz times
  geodesic distance pi).
- So measured columns are **lower bounds** on the Lean columns.
- **Refute (sound):** if the lower confidence bound of `sum_z TV_meas` exceeds 1 at one background, then `sum_z dob(x, z) > 1`. The
  column hypothesis of `mixing_rs_dobrushin` / `spectral_gap_dobrushin` (finite S; for SU(2) through Glauber's `hcol`) fails for the
  3^4-torus coarse specification. Likewise for the W1 column and `SiteInfluenceW` / `LimitDprimeW`. This is a provable existence
  statement: a bad boundary exists.
- **Discharge (impossible):** an upper bound on a lower bound bounds nothing. A small-box PASS discharges no Lean hypothesis.
- **One-box reading:** with `Lambda_0` = one cell, the box law of cell `x`'s full content given the outside cells' full contents
  dominates the coarse law of `V_x` (a function of the content), and the measured move of `V_z` is a mixture of full-content moves. So
  `TV_meas <=` the one-cell box's pair influence `kappa(z)` in `FineOneBox`. A refutation of the one-cell one-box sum is sound; larger
  boxes are untouched (`FineOneBox` asks for some box).

**Expected outcome** (fitted action, numerical):
- sharp sup-form pair coefficients (N2): ss 0.0735, ts 0.023;
- lower-bound columns: TV about 0.88 (12 ss) + 0.14 (6 ts) = 1.02 at the zero-rest-field worst case;
- at typical backgrounds (rest field `|A| ~ 0.8`) the TV per pair is about 15-30 % lower, so about 0.75-0.9;
- W1 per radian via the flip (chord): 12 x 0.0305 = 0.37;
- via the 0.5 rad move: 12 x 0.0486 = 0.58.

So a **TV refutation at a typical background is predicted not to occur**, unless the true law couples more strongly than the fit
(possible: the fit's closure residuals were 67 %). The one informative outcome is "true sup-form TV column > 1 at a typical background".
That would show directly that the sup form fails at `L1`, which the fit already makes likely (1.02 at the worst case).

## 4. Projection (`c9a-crossover/w2/PROJECTION.md` section 8's rule; inputs marked)

Sample sizes per ensemble (two ensembles per pair; the `D^2_U`/`Q_U` floor at the fitted law, exact quadrature, inline check):

| move | quantity | +-10 % | +-30 % |
|---|---|---|---|
| W1 move 0.5 rad | `KR_D` (0.0243) | 1.4 x 10^5 | 1.9 x 10^4 |
| antipodal flip | `KR_D` (0.0958; a lower bound on the per-radian coefficient as chord/pi) | 8.9 x 10^3 | 1.0 x 10^3 |

Per-trajectory cost (B = 1):

| variant | force | `eps`, `nleap` | s / trajectory | `tau` | `t_eff` |
|---|---|---|---|---|---|
| V1: `beta = 2.3`, `b = 8`, 24^4, float32 | 0.33 s (float64, plumbing) x 0.6 (float32: assumed, 1.0 +- 0.3) = 0.2 s | 0.002, 250 (the timing job's `dH ~ eps^2` extrapolation) | 55 s | 1.8 (T-B', marked) | 200 s |
| V2: `beta` about 2.15, `b = 4` (`L1 sqrt(sigma)` about 2.4-2.8; the scaling window's edge), 12^4 | about 0.17 s (GPU, interpolated from the 8^4 / 24^4 plumbing) | 0.0125, 40 (T-B' at `beta = 2.3`, transfer factor 1.0 +- 0.3) | 7.5 s | 1.8 (marked) | 27 s |

Ensemble cost and sets (central = x 1.33; band x [0.9, 1.9]; +25 % drift for runs much longer than the timed unit):

| set | V1 central (band) | V2 central (band) |
|---|---|---|
| one pair, flip +-30 % (2 ensembles, one background, one `kappa_c`) | 150 h (100-210) | **20 h (14-36)** |
| minimal set: 5 backgrounds x ss class x {none, flip} x 2 `kappa_c`, flip +-30 % (20 ensembles) | 1500 h (1000-2700) | **200 h (135-355)** |
| the same with the W1 move +-30 % | about 2.8 x 10^4 h | about 3.8 x 10^3 h |

(The V2 numbers carry the extra beta-transfer factor on `s_traj`: band about x [0.6, 2.5] when combined. Its `T(beta)`, the tuning
pre-step at `beta = 2.15`, must be measured on the CPU first (minutes, as T-B'); it is not.)

**Stop rules that apply:** `PREREG-PILOT2.md`'s cost-growth rule (3 times the projection), an unresolved `tau_int` stop, and the GPU
memory limit (24^4 at float32 fits easily; 12^4 trivially).

## 5. Recommendation and what would change it

1. **No GPU run for the small box in this form.** By the provability rule it can only refute. The fitted action predicts no refutation
   at typical backgrounds, and a PASS discharges nothing. 20-200 GPU-hours for an expected null outcome is poor value.
2. **The cheap, informative pieces are on the CPU:**
   - (a) the V2 tuning pre-step at `beta` about 2.15, `b = 4` (minutes; it fixes `T(beta)` and the step, so any later decision rests
     on measured numbers);
   - (b) **condition A's conditional mass** `m L1` from existing configurations, the one number that moves the analytic tail's
     boundary. If `m L1 >= 12`, the inside part shrinks to `d <= 2` (plaquette, rectangle and next shells); at about 6 it reaches
     `d <= 4`.
3. **What would make a GPU run worth it:** a reason to expect the true inside coupling well above the fit (for example from the
   crossover session's near-cut percolation at `beta = 2.3`). Then the TV refutation at one background (V2, about 20 h) could show that
   the sup form fails at `L1` for the true law: a provable negative statement about the coarse specification.
4. **The positive direction needs mathematics, not measurement:** a worst-case argument for the inside part (`NOTE.md` 2(a)), now
   localised to cell distance `<= 4` (`<= 2` if `m L1 >= 12`) and to the dichotomy's two inside events.

## 6. Not checked / open

- Condition A and `m L1` (open; the Poincare value `2 pi` is recalled, not derived for this blocking).
- Lemma C at the cell scale (open).
- The float32 factor and the GPU force at 12^4 (assumed, interpolated).
- The step at `beta = 2.15` (transferred from 2.3).
- `tau` at `b = 8` (T-B''s `b = 4` value used, marked).
- The typical-background TV reduction (15-30 %) is a rough reading of N2's `|A|` dependence, not computed here.
