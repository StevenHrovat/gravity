# The one-box statement as twist-sector equidistribution (GRH's shape) (2026-11-23)

Task (owner: "The features of the GRH also explain the properties of the HTF, since it gives uniform global smoothness from asserted
local correctness"; "Yes, do it"; via the coordinator):
1. Lean, the Fourier lemma: equidistributed twist sectors imply electric suppression, with explicit constants, tied to the converse;
2. the cancellation contrast: does the signed Fourier sum bypass the path-entropy barrier, or does positivity block it?;
3. a test on the small-torus data, pre-registered and exploratory;
4. a DMP section.

## 1. PRE-REGISTRATION of the exploratory test (fixed before the β = 3.5, `L ≥ 4` twist ratios were looked at)

**Disclosure.** Before this rule was written I had already seen the single-sector twist ratios at β = 2.3 for `L = 2, 4, 6` (both
tori; `SATURATION.md` 4) and at β = 3.5 for `L = 2` (`CONTAINMENT.md` 1). For those the test is **post hoc**. Unseen when this was
fixed: β = 3.5 at `L = 4` and `L = 6`. The test is **EXPLORATORY** in every case and enters no verdict.

* **What is measured.** The run measures one twist sector, a single temporal plane `(0, 3)`, on `L⁴` and `L³ × 2L`. By the
  hypercubic symmetry of `L⁴` the three single-plane temporal twists are equal there. Multi-plane sectors are **not** measured, so
  equidistribution across all `2ⁿ − 1` sectors cannot be tested; only the single-sector deficit can.
* **Quantity.** The equidistribution error of the single sector, `δ(L) = 1 − r(L)`, `r = Z_tw/Z` from the snake, on the cubic torus
  `L⁴`, `L = 2, 4, 6`, per β.
* **Errors.** `σ_δ = r · σ_stat(log r)` (statistical, jackknife within ensembles, variances added over snake steps). Also reported:
  the universal-floor version with the resolution floor of 1 on `log r = −F_tw`, my reading for a log-ratio over extent `L`
  (`ONEBOX-CHECK.md` 8.3).
* **Classification** (weighted least squares of `log δ` on `log L` over the three `L`, slope `s` with its statistical error; only
  points with `δ > 2σ_δ` enter):
  - **floor-like (square-root type):** `s ∈ [−1.5, −0.5]` (about `L^{−1}`, the square root of the `L²` plaquettes of the twist
    surface);
  - **faster than a floor:** `s < −1.5`, with `s + 2σ_s < −0.5`;
  - **no decrease:** `s > −0.5`, with `s − 2σ_s > −1.5`;
  - otherwise **unresolved**. With fewer than two usable points: **unresolved**.
* **Reading rule.** This is a three-point slope on tiny lattices. Whatever the class, it says nothing about large `L` or about the
  continuum. It can only contradict "the deficit does not decrease at small `L`".

Code: `w2/equidist_test.py` (written after this section).

---

Marks for the rest: **Lean** (`Crossover/Equidist.lean`, 9 theorems; `axioms-dy.log` now 65 Crossover theorems, standard axioms
only), **paper**, **sketch**, **exploratory numerical**, **open**.

## 0. Verdict in plain words

* **1. The Fourier lemma is in Lean, from the characters up.** The characters of `(ℤ/2)ⁿ` are orthogonal (`sum_chi`). 't Hooft's
  electric partition functions `Z_e(e) = 2^{−n} Σ_k χ(k, e) Z_k` satisfy `Σ_e Z_e = Z_0` and `Z_e(0) = 2^{−n} Σ_k Z_k`. Hence
  `(1 + S_tw)(1 + S_e) = 2ⁿ` (`sector_product`, now proved rather than quoted). If every twist ratio is at least `1 − δ`, the
  summed electric weight is at most `(2ⁿ − 1)δ/(2ⁿ − (2ⁿ − 1)δ)` (`electric_sum_le_of_equidist`, sharp). Each single electric
  sector is at most the summed twist deficits over `2ⁿ` (`elecZ_le_deficit`). With `electric_sum_lt_one_iff` (`Runs.lean`), the
  two directions are tied: summed electric weight below 1 iff the summed twist weight exceeds `2^{n−1} − 1`.
* **2. The cancellation is real, but it is not a new resource.** In deficit variables `d_k = 1 − Z_k/Z_0`, which are `≥ 0` by
  reflection positivity (`Z_tw ≤ Z`), the summed electric weight is exactly `S_e = Σ d_k / (2ⁿ − Σ d_k)`, a function of the
  **sum of nonnegative deficits** only. The signed Fourier sum cancels exactly as much as the deficits are small; no signed
  quantity is left over to exploit.
  - *Does it bypass the path-entropy barrier?* Yes for the electric channel **at one box**: the box's electric suppression follows
    from that box's twist deficits, with no sum over paths of smaller boxes.
  - *What it costs.* It moves the requirement to twist saturation at the scale of the distance. That is 't Hooft's criterion
    (`FlipSat`, `F_tw → 0`), the confinement statement itself, now needed as a **lower** bound on twist partition functions.
  - *Positivity.* It does not block the identity. It supplies exactly the signs that make every term absolute (`d_k ≥ 0`,
    `Z_e ≥ 0`). It cannot supply the content: reflection positivity proves twist ratios `≤ 1`, never close to 1.
  - *Where the GRH-type cancellation does live.* Along the snake: `log r = Σ_{m=1}^{L²}` of local single-plaquette terms. Opening the
    twist surface costs (an open 't Hooft loop), closing it pays back. Saturation means these `L²` local terms cancel to `O(δ)`. That
    is a growing-`N` cancellation, the shape of RH's square-root bound, but it is a statement about one box's surface free energy,
    not a composition rule.
* **3. Exploratory test (rule fixed before the unseen numbers).**
  - *β = 2.3:* the deficit decreases. With the two resolved points (`L = 2, 4`; `L = 6` has `δ < 2σ`) the slope is `−0.62 ± 0.18`,
    "floor-like" by the pre-registered class. Post hoc for this β, and unresolved under the resolution floor of 1 on `log r`.
  - *β = 3.5 (unseen before the rule for `L = 4, 6`):* no decrease, `δ = 0.98, 0.97, 0.96`, slope `−0.016 ± 0.009`, robust under
    the floor. Boxes up to `L = 6` are still inside the weakly coupled container at β = 3.5 (twist rare, `r` = 0.018 to 0.039): the
    "outside" of `CONTAINMENT.md` (a).
* **First unclosable step:** a **lower** bound on the twist ratios (deficits `Σ d_k < 2^{n−1}`) at one box of fixed physical size.
  This is the same step as in `SATURATION.md` and `CONTAINMENT.md`, now in GRH's form: local positivity is given, and the global
  cancellation (the closing of the twist surface) has to be proved.

## 2. The Fourier lemma (Lean)

| statement | Lean name | mark |
|---|---|---|
| `Σ_x (−1)^{a x} = 2` if `a = 0`, else `0` (`x ∈ ℤ/2`) | `sum_sgn2` | Lean |
| `χ(k, e) = χ(e, k)`; `|χ| = 1` | `chi_comm`, `abs_chi` | Lean |
| `Σ_e χ(k, e) = 2ⁿ [k = 0]` | `sum_chi` | Lean |
| `Σ_e Z_e(e) = Z_0`; `Z_e(0) = 2^{−n} Σ_k Z_k` | `sum_elecZ`, `elecZ_zero` | Lean |
| `(Σ_k Z_k/Z_0)(Σ_e Z_e/Z_e(0)) = 2ⁿ` | `sector_product` | Lean |
| `Z_k ≥ (1 − δ) Z_0` for all `k ≠ 0` ⟹ `S_e ≤ (2ⁿ − 1)δ/(2ⁿ − (2ⁿ − 1)δ)` | `electric_sum_le_of_equidist` | Lean (sharp) |
| `e ≠ 0` ⟹ `Z_e(e) ≤ 2^{−n} Σ_k |Z_0 − Z_k|` | `elecZ_le_deficit` | Lean |

For small `δ`, `S_e ≈ (1 − 2^{−n}) δ`. The identification of `Z_k` with the SU(2) twisted partition functions and of `Z_e` with the
electric-flux sectors is 't Hooft's, as in `Flip/Floor.lean` and `Attempts/R4/LayerSector.lean` for one sector.

## 3. The cancellation contrast (paper)

* **The identity in deficit form.** With `d_k = 1 − ρ_k`, `ρ_k = Z_k/Z_0 ≤ 1` (reflection positivity, every central twist), and
  `D = Σ_{k≠0} d_k ∈ [0, 2ⁿ − 1)`: `1 + S_tw = 2ⁿ − D`, so `S_e = 2ⁿ/(2ⁿ − D) − 1 = D/(2ⁿ − D)`. Every quantity is nonnegative.
  The "cancellation" in `Σ_k (−1)^{k·e} ρ_k` is exactly `D` being small.
* **Against the path sums of `CONTAINMENT.md`.** Path sums compose per-box costs over many boxes and pay the path entropy `log μ`.
  The Fourier identity composes nothing: it relates two sectors of **one** box. So the electric suppression of a box of size `D`
  needs that box's twist saturation, with no path sum and no entropy, but at the scale `D` itself. The barrier is not bypassed; it
  becomes "twist saturation at the target scale" (`FlipSat` along the scales, 't Hooft's criterion, `Flip/Floor.lean`).
* **Positivity.** Reflection positivity gives `ρ_k ≤ 1` and `Z_e ≥ 0`: the right signs for the identity, the wrong direction for the
  content. A lower bound on `ρ_k` is a lower bound on a twisted partition function relative to the untwisted one. That is what every
  attempt so far has needed and not had (Tomboulis's interpolation, `SATURATION.md` 2).
* **Where cancellation of growing size lives (sketch).** The snake writes `log r` as a sum of `L²` local terms
  `log⟨e^{−βq_m}⟩ − log⟨e^{βq_m}⟩`. The partial sums are free energies of open 't Hooft loops: they grow while the open surface's
  boundary grows, then the closing steps pay them back. A saturated box (`r ≈ 1`) is one where `L²` local terms of both signs cancel
  to a small total. That has RH's shape: local terms of size `O(1)`, many of them, a global total far below their count. But it is a
  property of one box's twist free energy, and proving the cancellation is the lower bound above.
* **The electric channel versus the neutral sector.** Even full twist saturation gives the electric (centre-charged) channel. The
  neutral sector of the mass gap enters through the excess act `c(L)` (`HTF.md` 4), as before.

## 4. Exploratory test result (`w2/equidist_test.py`, CPU seconds, `w2/runs/equidist_test.json`)

| β | `L` | `r` | `δ = 1 − r` | `σ_δ` (stat) | `σ_δ` (floor 1 on `log r`) | seen before the rule? |
|---|---|---|---|---|---|---|
| 2.3 | 2 | 0.116 | 0.884 | 0.010 | 0.116 | yes |
| 2.3 | 4 | 0.425 | 0.575 | 0.073 | 0.425 | yes |
| 2.3 | 6 | 0.863 | 0.137 | 0.229 | 0.863 | yes |
| 3.5 | 2 | 0.018 | 0.982 | 0.002 | 0.018 | yes |
| 3.5 | 4 | 0.027 | 0.973 | 0.007 | 0.027 | **no** |
| 3.5 | 6 | 0.039 | 0.961 | 0.015 | 0.039 | **no** |

| β | statistical errors | universal floor |
|---|---|---|
| 2.3 | 2 usable points (`L = 6` below 2σ): slope `−0.62 ± 0.18`, **floor-like** (post hoc) | 1 usable point: **unresolved** |
| 3.5 | 3 points: slope `−0.016 ± 0.009`, **no decrease** | slope `−0.018 ± 0.034`, **no decrease** |

**Reading (exploratory).** At β = 3.5 the boxes `L ≤ 6` are inside the container: the twist is rare and its deficit does not move.
At β = 2.3 the deficit falls from 0.88 to 0.58 to about 0.14. The resolved part is consistent with an `L^{−1}`-type decrease, and
the unresolved `L = 6` point lies below that trend. Three points on tiny lattices; no statement about large `L`.

## 5. DMP reading (separate; not mathematics)

* **Local correctness, global smoothness.** In GRH each Euler factor is a correct local statement, and the global error is the square
  root by cancellation. Here each twist sector is a correct local statement, `Z_k ≤ Z_0` by reflection positivity: local positivity,
  asserted and proved. Global smoothness is equidistribution of the sectors, and by `sector_product` it is exactly the electric
  suppression. The owner's sentence maps one to one.
* **The same open half as GRH.** In both problems the local positivity is in hand. What is missing is the global inequality: Weil
  positivity for GRH; for Yang-Mills, the lower bound that makes the twist surface close with only a small remainder. The HTF is smooth
  exactly when its twist surfaces close; that is the proof obligation, not a consequence of local correctness alone.
* **Inside and outside the container.** The test shows both regions: at β = 3.5 and small `L` the remainder stays (non-existence
  kept by assertion, twist rare); at β = 2.3 it shrinks with `L`.

## 6. Status

| step | result | mark |
|---|---|---|
| characters, orthogonality, electric sectors, sector product | closed | Lean |
| equidistribution (`ρ_k ≥ 1 − δ`) ⟹ `S_e ≤ (2ⁿ − 1)δ/(2ⁿ − (2ⁿ − 1)δ)` (sharp); per-sector bound by deficits | closed | Lean |
| converse tie (`S_e < 1 ⟺ S_tw > 2^{n−1} − 1`) | closed | Lean (`Runs.lean`) |
| cancellation contrast: identity in nonnegative deficits; bypasses path sums at one box, moves the requirement to twist saturation at the target scale | answered | paper |
| **lower bound on twist ratios (`Σ d_k < 2^{n−1}`) at one box of fixed physical size** | **first open step** | open |
| exploratory test: β = 2.3 decreasing (floor-like on 2 points, post hoc); β = 3.5 no decrease (unseen) | | exploratory numerical |

## 7. Files

* `EQUIDIST.md` (this note; section 1 pre-registered); `formal/ProofPhase/Crossover/Equidist.lean` (new, 9 theorems); `axioms-dy.sh`
  extended, `axioms-dy.log` (65 theorems, standard axioms); `w2/equidist_test.py`, `w2/runs/equidist_test.json`; `~/formal-dy`
  deleted.

## 8. Addendum: the sign flip at a DB, positivity of the sectors, and uniformity over outsides (2026-11-23)

The owner, on positivity against cancellation: "It only does so by inverting and sign flipping it through the rotation that
happens as an act at a DB, this gives the needed features." The coordinator's mapping: (i) the sign `(−1)^{k·e}` is a `ℤ/2`
character, and the twist is the centre element `−1` of SU(2), the rotation by `2π` (the spinor sign); (ii) each electric sector
`Z_e` is itself nonnegative, a projected trace, and it equals a signed sum of nonnegative twisted ratios. So cancellation happens
inside a positive quantity.

### 8.1 Check of (i) and (ii) (paper; Lean where marked)

* **(i) holds.** The twist inserts the centre element `−1 ∈ SU(2)` on the twist surface (`flipG`, `negOneSU2` in
  `Flip/Strict.lean`). As an SO(3) rotation it is the identity; as an SU(2) element it is the rotation by `2π`, the spinor sign. The
  character `χ(k, e)` is the sign the electric sector `e` picks up under the twists `k`.
* **(ii) holds on the torus.** In temporal gauge with the transfer matrix `T`, positive by reflection positivity, the centre
  transformations `Ω̂_k` commute with `T` and with the Gauss projection `P_G`. `P_e = 2^{−n} Σ_k χ(k, e) Ω̂_k` is an orthogonal
  projection (the characters are orthogonal: `sum_chi`, Lean), and it commutes with `T`. So
  `Z_e = tr(P_e P_G Tⁿ) = tr((T^{n/2} P_e P_G)* (T^{n/2} P_e P_G)) ≥ 0`, while `Z_k = tr(Ω̂_k P_G Tⁿ)`, and
  `Z_e = 2^{−n} Σ_k χ(k, e) Z_k` (`elecZ`). For one sector this is in Lean
  (`Attempts/R4/LayerSector.lean`: `Z = Z₀ + Z₁`, `Z_tw = Z₀ − Z₁`, `Z_tw ≥ 0`). **So positivity bounds `Z_e` below by 0 and does
  not block its smallness.** That agrees with section 3: positivity supplies the signs, not the content.

### 8.2 The real question: does the sector cancellation replace the path sum for the one-box statement? (paper)

**No. The grid requirement returns once the box's electric flux must be bounded uniformly over its outsides.** Three reasons, each
exact:
1. **With a fixed outside, a twist of the box is a change of the outside.** A twist surface through the box ends on the collar.
   By the flux identity (`cob_restrict_eq_cob_restrict_compl`, Lean), inserting it is the same as changing the outside's flux
   through the box: `Z_k(σ) = Z(σ_k)`. So the twist ratios of a box with outside `σ` compare the box under **different outsides**.
   Making every deficit `1 − Z(σ_k)/Z(σ)` small, uniformly in `σ`, is exactly the box's insensitivity to the outside's flux on each
   face. That is the summed influence over the faces, the quantity of `NEIGHBOURS.md`.
2. **The number of sectors grows with the boundary.** On the torus `n` is fixed (the cycles: `n ≤ 6`). With an outside, the sectors
   are the closed flux patterns the outside can put through the box surface. At face resolution these are the even subsets of the
   `2d` faces, `2^{2d−1} = 128` sectors in `d = 4` (`N = 2d − 1 = 7` independent ones); at cell resolution `N` grows with the box
   surface. The exact sector product then reads `(1 + S_tw(σ))(1 + S_e(σ)) = 2^N` wherever the projections exist. Duality caps the
   smaller sum only at `2^{N/2} − 1` (`min_le_of_sector_product`, Lean): 10.3 at face resolution. Electric suppression
   (`S_e < 1`) needs a mean twist ratio above `(2^{N−1} − 1)/(2^N − 1)`: 63/127 ≈ 0.50 over 127 sectors, for every outside. The
   count of faces is back, now as the number of sectors.
3. **Positivity is lost at a fixed outside.** Reflection positivity applies to traces and to reflection-symmetric boundary
   conditions. For an arbitrary outside, neither `Z(σ_k) ≤ Z(σ)` nor the positivity of the projected sums holds in general: the
   deficits can have either sign, and the sector sums are genuinely signed. That is where the owner's sign flip at a DB could act,
   and also why no positivity argument can certify the uniform smallness. It is a supremum over outsides of signed sums, the
   one-box condition's original form.

**What the sector cancellation does give.** For the **annealed, periodic** quantities (`F_e` of a periodic box), it replaces the path
sum exactly: one box's electric suppression is one box's twist equidistribution, with no composition and no entropy. For the
**quenched** one-box statement it is a reformulation. The faces come back as sectors, and positivity, the only general tool for
signs, does not reach a fixed outside.

**First unclosable step, sharpened.** Uniformly over well-defined outsides `σ`: the box partition function is nearly insensitive to
the outside's flux pattern, `|1 − Z(σ_k)/Z(σ)|` small for all `2^N − 1` closed boundary patterns `k`, with mean deficit below about
`1/2` at face resolution. This is the summed-influence condition in sector form, with the sign structure the owner names. Proving it
needs a worst-case argument at one DB, not positivity.

### 8.3 DMP reading (separate)

* **The rotation at a DB is exact.** The act at a DB that inverts and flips the sign is the centre element `−1`, the `2π` rotation
  that only spinors see. The electric sector is what survives the sign-weighted average over these rotations. Each sector is
  nonnegative, so the cancellation lives inside an existing quantity, as the owner says.
* **Where it gives the needed features, and where not yet.** On the closed (periodic) system the flipped and unflipped sides
  balance exactly into nonnegative sectors: the cancellation is free and complete. At one DB with an arbitrary outside, the flip is
  a change of the outside. The box has to treat all its outsides' flips alike, and that uniformity, across as many sectors as the DB
  has faces, is the proof obligation that remains.
