# No trapping: what holds, what does not, and the lemma it reduces to (m1-tools, 2026-11-22)

Brief: attempt a proof that the twisted blocking has no trapping (every deep core at a block centre is either labelled
or becomes moderate), or reduce it to the sharpest named lemma; and run the `d = 4`, `L = 13` test that the full lattice
could not reach (`TWIST.md` 5). CPU only. Scripts and logs in this folder: `offcentre_L13.py`
(`run_offcentre_L13.log`), `notrap_search.py` (`run_notrap.log`), `notrap_longsearch.py` (`run_notrap_long.log`),
`cut_avoidance.py` (`run_cut_avoidance.log`), `cut_adversarial.py` (`run_cut_adversarial.log`). Each script states its
question in its header, written before running. Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **At realistic block size the off-centre step is harmless (`d = 4`, `L = 13`, exact paths).** A deep core of any
   kind at any off-centre site of a block becomes moderate in one blocking step: over 21744 cores (vortex patterns,
   random stars, random values on 1-3 bonds; every site within distance 2 of the centre and 3000 random sites), the
   largest coarse spread was 0.099, nothing deep, nothing trapped. Even next to the centre only 12.5% of the paths pass
   through a site (`1/(2d)`), and the fraction falls to 2% at the block's edge. The smearing seen at `L = 3`
   (`TWIST.md` 4) was a small-block effect.
2. **Locally the star map contracts very strongly (numerical).** For stars of spread up to 1.5 rad the worst one-step
   ratio found (random samples plus local search) is 0.11; it scales like `0.075 × spread`. Random deep stars are
   captured (moderate or labelled) within 6 steps, mean 2.5.
3. **But uniform no trapping is not true as stated, or at least has no support.** An adversarial search finds deep,
   non-centre-valued stars that escape only slowly: by tuning the start to about `3·10⁻⁵`, capture times reach 15 and
   keep growing with finer tuning. The configurations it approaches are "balanced": each bond's logarithmic average of
   the others, seen from itself, nearly vanishes, so the average barely moves them. They are unstable (they need fine
   tuning) but there is no uniform bound on the capture time. Like the vortex (`NOTE.md` 2.4), this is a property of
   averaging on SU(2), not a bug of the rule.
4. **No trapping is not what M1 needs.** Under the root rule a pinned core is charged once and carried. It costs little
   per step (P2′) **as long as Balaban's average is analytic at its star**, which fails only near the logarithm's cut.
   The balanced stars are far from the cut (relative angles about 60-120 degrees), so they can be carried like
   labelled cores, captured or not. The requirement is therefore **cut avoidance**, not capture.
5. **Cut avoidance, numerically.** With the Z2 label chosen once at the root (the sign pattern that minimises the
   largest relative angle), the largest corrected relative angle is at most 138 degrees on random stars and 147 degrees
   adversarially (33 degrees from the cut). Along orbits it can grow, adversarially up to 171 degrees, but such visits
   are single steps: even an adversarial search never found more than **1 step in 31** above 160 degrees.
6. **The sharpest named lemma (Lemma NT′, open, numerically supported):** (a) every 8-element star has a sign pattern
   with all corrected relative angles `≤ θ_root < π`; (b′) along the orbit of the corrected star under Balaban's star
   map, at most `N_cut` steps over the whole orbit have a relative angle `> π - δ0` (numerically `θ_root ≈ 147°`,
   `δ0 = 20°`, at most 1 such step in every 31-step orbit tested). With NT′, every pinned core is carried analytically except at isolated near-cut steps, each paid
   at polylogarithmic cost by the root suppression; no capture lemma is needed. A proof of NT′(a) looks within reach
   (a covering argument on the projective space of SU(2)); NT′(b) does not yet have a proof idea beyond the observed
   expulsion from the cut.

## 1. The off-centre step at `L = 13`, `d = 4` (`offcentre_L13.py`)

Exact contour family of [I] (0.4): all `541k` paths `Γ ∈ G(Y, x)`, `x ∈ B(Y)`, with the segment to the next block
(paths in the next block never meet `B(Y)`; the bonds `(Y, Y - L e_a)` by reflection symmetry). A core at site `z` is a
star of 8 group elements at `z`; everything else trivial (the shell's effect was tested in the one-site model, `P0.md`).
For each path through `z` the transport is the product of `g_in⁻¹ g_out` over its visits (double visits handled).

| distance of `z` from the centre | path fraction `f(z)`, max over the 8 coarse bonds | median |
|---|---|---|
| 1 | 0.125 | 0.0011 |
| 2 | 0.104 | 0.0010 |
| 3 | 0.084 | 0.0005 |
| 6 (block edge) | 0.021 | 0.0005 |

| cores (3 per site and kind) | n | moderate | labelable | deep | largest coarse spread |
|---|---|---|---|---|---|
| distance `≤ 2`, vortex pattern | 1872 | 1.000 | 0 | 0 | 0.000 (erased exactly) |
| distance `≤ 2`, Haar star | 1872 | 1.000 | 0 | 0 | 0.072 |
| distance `≤ 2`, Haar on 1-3 bonds | 1872 | 1.000 | 0 | 0 | 0.079 |
| 3000 random sites, each kind | 3 × 9000 | 1.000 | 0 | 0 | ≤ 0.099 |

Together with the centre case (one-site model at `L = 13`) this closes, numerically, the gap the `d = 4` full-lattice
test left: an off-centre core is diluted to a spread below 0.1 in one step, and from then on it is a moderate core
(Lemma D-mod).

## 2. Local contraction and capture (`notrap_search.py`)

| spread `≤` | 0.3 | 0.6 | 0.9 | 1.2 | 1.5 |
|---|---|---|---|---|---|
| worst one-step spread ratio found | 0.0058 | 0.0235 | 0.048 | 0.079 | 0.113 |

(`L^{1-d} = 0.00046` is the linear rate; the rest is the nonlinear term, `≈ 0.075 × spread`.) **NT1 (local
contraction), paper sketch:** for a star in a ball of radius `r < π/2`, one step of the log-average from each reference
point lands within `C r² · spread` of the common Karcher mean, plus the `L^{1-d}` spread of the weights; the numbers
give `C ≈ 0.075` up to spread 1.5. A proof would use comparison geometry on `S³`; not written.

Capture of 20000 random (Haar) stars: times 1: 202, 2: 11239, 3: 7585, 4: 910, 5: 63, 6: 1; never more than 6.

## 3. The adversarial search and the balanced stars (`notrap_longsearch.py`)

Hill climbing on the star (100 starts, 300 iterations, step size adapted) to maximise the capture time: maximum 9 after
100 iterations, 11 after 150, 12 after 200, 15 after 300, with the step size of the best start down to `3·10⁻⁵`. The
worst star's relative angles change by 1-3 degrees per step (largest 121-154 degrees, one nearly coincident pair, the
rest 60-120 degrees): it drifts slowly near a balanced configuration. For an exactly balanced configuration (for example
a regular simplex in `S³`, where the tangent vectors from each vertex to the others sum to zero) the log-average from
each point is the point itself, so such configurations are fixed points of the uniform-weight map; the small
differences of Balaban's weights (`L^{1-d}`) move them slowly. Escape rate near the worst found: about a factor 2 per
step. Consequence: no uniform bound on capture times; the Haar tail decays by about a factor 10 per step.

## 4. Cut avoidance (`cut_avoidance.py`, `cut_adversarial.py`)

Label chosen once at the root: the sign pattern (128 choices modulo a global sign) minimising the largest corrected
relative angle. Then the corrected star evolves by Balaban's map (`P0.md` 1).

| check | random stars | adversarial |
|---|---|---|
| (i) largest corrected angle at the root | max 138.2°, median 116.6° (5000) | 147.1° (200 climbs) |
| (ii) one-step increase of the largest angle | — | up to +22.2° (from 129.7°): no monotonicity |
| (iii) largest corrected angle along a 30-step orbit | max 138.2° (equal to the root value in all 5060 stars tried, slow stars included) | 171.4° (8.6° from the cut) |
| (iv) steps (of 31) with a corrected angle above 160° | 0 | at most 1 |

(A first run of (iv) had a flat objective and found 0; the rerun adds the orbit maximum as a tie-breaker.)

**Lemma NT′ (cut avoidance), open.** (a) Root bound: for every star of `2d` elements of SU(2) there is a sign pattern
with all corrected relative angles `≤ θ_root < π`. (b′) Few near-cut steps: along the orbit of the corrected star under
Balaban's star map (and under small shells), at most `N_cut` steps over the whole orbit have a relative angle
`> π - δ0`.

**Why NT′ suffices (paper).** A pinned core is a root (charged once, `D-PIN.md` 3-4). At steps where its corrected star
is within `π - δ0` of the identity, Balaban's average is analytic with radius `≥ c δ0`, far above the analyticity
radii Balaban needs (`α_{0,k} = g_k C0 (log g_k^{-2})^{q0}`), so the surroundings are renormalised analytically and the
core is carried at the cost of P2′. At a near-cut step the region around the core is carried as a Balaban large-field region for that step (cost
`O(1) M^d R^{d+1}`, polylogarithmic). A bound of the form "at most `n_cut` near-cut steps per window of `n`" would give
an extra cost linear in the core's age, which the root suppression pays only through asymptotic freedom
(`a/g_h² ≥ a b (k - h) log L`), and that fails against a polylogarithmic cost per step for small `g`. So (b) must be
stated over the whole orbit: **(b′) at most `N_cut` near-cut steps over the whole orbit of a pinned core.** Then the
extra cost is `N_cut · polylog ≪ a/g_h²`. Numerically consistent: no orbit had more than one near-cut step in 31, and
once the corrected spread is below about 1.5 rad the orbit contracts monotonically (section 2) and cannot return near
the cut. Not covered by the numerics: the slow balanced stars stay at spreads of about 2 rad for long times; their
largest angles (121-154° in the worst one) stay below the 160° threshold in the runs, but longer orbits were not tested.

**Attempt at (a).** The 8 points of SU(2) modulo sign lie in the projective space `RP³`, where any two are at most
`π/2` apart. A lift with all pairwise angles `≤ θ` exists iff the points can be lifted into a common open half-space
"cone" of angular radius `θ/2`; a covering argument on `RP³` with 8 points gives some `θ_root < π`, but a clean value has
not been derived. Numerically `147°` is the worst found. Open (short).

## 5. Status for the paper

* §5.3 of the outline (`M1-PLAN.md`) changes from "no trapping" to "cut avoidance": the capture statement is replaced
  by Lemma NT′ (a, b′), with the off-centre step (section 1) and local contraction (section 2) as supporting results.
* What is proved: nothing new in this note is a proof. What is numerical and adversarially checked: the off-centre step
  at `L = 13`, local contraction, the root bound (a), short near-cut episodes. What is false: uniform capture (or at
  least unsupported: there are slow balanced stars).
* Next: prove NT′(a) (covering on `RP³`); try (b′) via the expulsion mechanism (near the cut the average jumps,
  `D-PIN.md` 2.3) combined with local contraction (once the spread is below about 1.5 rad the orbit contracts and never
  returns).
