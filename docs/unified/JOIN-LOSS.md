# O1 split into the electric side and the join loss: what the tools give (join-loss round)

Status: 2026-11-23. Proof-focused round on the Yang-Mills open step O1, in the split form of `OPEN-STEPS-DMP.md` 1(b)-(d).
**O1 is not proved.** Nothing here proves it in four dimensions with outsides.

Lean: `ProofPhase/Unified/JoinLoss.lean`, `ProofPhase/Unified/JoinLossSlab.lean` (42 declarations, standard axioms only, no
sorry: `joinloss-axioms.sh`, `joinloss-axioms.log`). Third layer (refute-only): `join_loss_check.py`, `join_loss_check.log`
(CPU, about 2 seconds, saved data only, no new simulation).

Status marks as in `OPEN-STEPS-DMP.md`: **Lean**, **classical**, **recalled**, **external**, **numerical**, **reading**,
**open**, **fails**.

---

## 0. In plain words

**The split is in Lean.** O1 at three hand-over lengths follows from two named statements (`ymOneBox_of_split`):
- **electric side:** the hand-over box is on the electric side, `F_e >= 0.881`, for every outside;
- **join loss:** joining two boxes in series loses at most `l`, for every outside.

**The threshold is 0.366, not 0.244.** Three boxes have two joins, not three. The 0.244 came from the iterated form
`k (F - 2C)` of `flux_superadd_iter`, which charges one loss per box. Charging one loss per join, three boxes clear the
floor while `l < 0.366`, four while `l < 0.538` (Lean: `ymOneBox_quarter` proves `l <= 1/4` suffices for every `mu <= 7`).

**What the tools give for the join loss.**
1. **On the torus (transfer matrix, reflection positivity): a two-sided bound by the remnant tails** (Lean,
   `joinLoss_bounds`). The loss is the neutral sector's join excess minus the charged sector's. Each excess is at least 0
   and at most the sector's remnant tail (the weight above its top eigenvalue). So
   `-(charged tail) <= loss <= (neutral tail)`, at each of the two boxes.
   - In 2D SU(2) the neutral tail alone already clears the floor, at every coupling and in the continuum [numerical].
   - In 4D on the saved small tori the neutral excess is large (1.27 at beta 2.3, `L = 4`), and the measured loss is
     near 0, because the charged sector carries almost the same excess [numerical, not certified].
   - So in 4D a bound has to capture a **cancellation** between the two sectors. The structure alone cannot: the loss
     can exceed any bound (Lean, `joinLoss_unbounded`).
2. **Reflection identity, chessboard estimate, Tomboulis-Yaffe: nothing more for the join loss.**
   - They give sector positivity and log-convexity, which is item 1's structure.
   - They treat both sectors alike, so they cannot sign a difference of the two.
   - Tomboulis-Yaffe composes costs without loss, but into a Wilson loop, not into `F_e` of a longer box.
3. **The boundary-uniform form has zero join loss: a theorem** (Lean, `elec_submul`). Take the electric factor
   pointwise, for every end-face outside, rather than averaged over a torus. Then joining two slabs through a shared face
   multiplies the factors exactly. The mixed sector terms cancel over the face. This needs one symmetry: the centre twist
   must commute with the slab. That holds in the **slab geometry** (the directions transverse to the twist plane
   periodic, so the outside is the two end faces).
   - Consequence (`three_slabs_O1`, Lean): three slabs on the electric side, uniformly over end-face outsides, give O1
     in its sector form for every `mu <= 14`. The join part is no longer open there.
   - With the single-layer floor (a twist changes a configuration's weight by at most `e^{-2 beta N}`), `n` layers have
     uniform electric factor at most `tanh(beta N)^n` (`kchain_tanh`, Lean). That is a rigorous, unconditional bound with
     no join loss, but the rate `log coth(beta N)` vanishes in the continuum.
   - In a box with fixed side outsides the symmetry fails at the side collar. The join loss returns as the cost of a
     seam of the twist sheet along the side. **open**
4. **Birkhoff-Hopf** applies in the same uniform form and contracts the twist cost. It needs the full projective diameter
   of one slab's kernel, which grows with `beta` times the face size. Rigorous only at strong coupling or for long slabs
   at fixed cross-section [classical].

**Was a rigorous bound reached?** Yes, three of them, all short of O1:
- the two-sided tail bound on the torus (any coupling; it clears only when the neutral tail is small, as in 2D);
- **zero join loss** in the boundary-uniform slab form (every coupling, every finite slab);
- the unconditional rate `tanh(beta N)^n`, which closes O1 in slab form only at strong coupling in tick units
  (`beta N <= 0.44` per layer for the electric side).

**What is left.** In the slab form, O1 reduces to the **electric side alone**: at the hand-over slab, the twist ratio
is at least `sqrt 2 - 1` for every end-face outside. That pointwise side is **stronger than the torus side**. In 2D the
uniform hand-over area is 2.8 times the torus one [numerical]. The open step has moved; it has not shrunk to nothing. In
the box geometry of the tube chain, the side seam is also open.

---

## 1. The split in Lean (task 1)

`JoinLoss.lean`, section 1. `F : N -> Omega -> R` is the electric cost of a box of length `n` (series direction) with
outside `omega`.

| statement | content | mark |
|---|---|---|
| `JoinLoss F L l` | for lengths `a, b >= L` and every outside `omega` of the joined box, outsides `omega1, omega2` of the parts with `F a omega1 + F b omega2 - l <= F (a+b) omega` | named hypothesis, **open** |
| `ElectricSide F L` | `F L omega >= log(1 + sqrt 2)` for every outside | named hypothesis, **open** |
| `series_bound` | `k` boxes: `F(kL) >= k s - (k - 1) l` | Lean |
| `three_boxes` | `F(3L) >= 3 s - 2 l` | Lean |
| `ymOneBox_of_split` | side + join loss + `log mu + 2 l < 3 log(1 + sqrt 2)` give `YMOneBox (F (3L)) mu` | Lean |
| `ymOneBox_lossless` | `l = 0`, `mu <= 14`, via `three_steps_clear` | Lean |
| `ymOneBox_quarter` | `l <= 1/4`, `mu <= 7` (`mu_4 = 6.77`): `mu e^{2l} <= 14 < 7 + 5 sqrt 2 = (1 + sqrt 2)^3` | Lean |
| `joinLoss_of_flux` | `flux_superadd`'s hypotheses with the neutral excess `c(n) <= C` give `JoinLoss` with `l = 2C` | Lean |

**So O1 at `3 L_h` is exactly these two named pieces.** The outsides of the parts are existential, because the parts of a
joined box see each other as outside. Uniform lower bounds pass through this unchanged.

**Thresholds per join** [Lean for the inequalities; numerical for the decimals, `join_loss_check.log`]:

| boxes in series | per-join threshold `(k log(1+sqrt 2) - log mu_4)/(k - 1)` | iterated form `log(1+sqrt 2) - log(mu_4)/k` |
|---|---|---|
| 3 | **0.366** | 0.244 |
| 4 | **0.538** | 0.403 |

`flux_superadd_iter` proves `F(kL) >= k (F(L) - 2C)`, which charges `2C` for `k` joins. The binary form
`F(a + b) >= F(a) + F(b) - 2C` iterates to `k F(L) - (k - 1) 2C`. The earlier 2D calibration already printed losses per
join with the `k - 1` count, so its margin was larger than stated.

---

## 2. What each tool gives for the join loss (task 2)

### 2.1 Transfer matrix and reflection positivity: the loss is a difference of two remnant tails (Lean)

**Setting** [classical; Lean for the algebra]:
- Take the series direction inside the twist plane (as for `L^3 x 2L` against `L^4`).
- On the torus, `Z_e(n) = Tr(P_e T^n)`, with `T` the positive transfer matrix (reflection positivity, Osterwalder-Seiler)
  and `P_e` the projector on electric flux `e`.
- So each sector is a power sum of nonnegative eigenvalues (`pZ`), and `F_e = log Z_0 - log Z_1` (`fluxF`).
- A join of lengths `a`, `b` is exactly the trace of `T^{a+b}`.

| result | statement | mark |
|---|---|---|
| `joinLoss_eq` | `l(a, b) = phi_0(a, b) - phi_1(a, b)`, `phi_e = log Z_e(a) + log Z_e(b) - log Z_e(a+b)` | Lean |
| `joinExcess_nonneg` | `phi_e >= 0` (power sums are submultiplicative, `sum_pow_add_le`) | Lean |
| `joinExcess_le_tail` | `phi_e(a, b) <= t_e(a) + t_e(b)`, `t_e(n) = log(Z_e(n)/lambda_e^n)` the **remnant tail** above the top eigenvalue | Lean |
| **`joinLoss_bounds`** | `-(t_1(a) + t_1(b)) <= l(a, b) <= t_0(a) + t_0(b)` | Lean |
| `tail_antitone`, `pZ_div_le` | the tail falls with the length, `Z(n)/lambda^n <= 1 + (d - 1) q^n` | Lean |
| `joinLoss_torus`, `ymOneBox_torus` | neutral tail `t_0(L) <= tau` gives `JoinLoss ... L (2 tau)`; with the side and `log mu + 4 tau < 3 log(1 + sqrt 2)`, O1 at `3L` on the torus | Lean |
| `joinLoss_unbounded` | neutral spectrum `1, 1/2 (d times)`, charged `1/4`: `l(1,1) >= log(1 + d/2)`, unbounded | Lean |
| `joinLoss_le_iff_oplus` | loss `<= tau` iff `elec c(a+b) <= e^tau elec(c(a) (+) c(b))`: the loss is the shortfall from the lossless point of the hyperbolic ledger | Lean |

**This is the owner's "tail of remnants," exactly** [reading]. With `lambda` the top neutral eigenvalue, `flux_superadd`'s
"neutral excess act" `c(n)` is the neutral remnant tail `t_0(n)`. The loss is bounded by the remnants above the ground
state, and it is reduced by the charged sector's own remnants.

**2D SU(2) calibration** (`join_loss_check.py` part A) [classical formulas; numerical]:

| beta | `A_h` | neutral tail `t_0(A_h)` | charged tail `t_1(A_h)` | loss `l(A_h, A_h)` | tail-only bound `2 t_0` | `t_0 < 0.183` (`ymOneBox_torus`) |
|---|---|---|---|---|---|---|
| 1.0 | 0.584 | 0.151 | 0.103 | 0.083 | 0.302 | yes |
| 2.3 | 1.115 | 0.132 | 0.071 | 0.109 | 0.265 | yes |
| 8.0 | 4.065 | 0.113 | 0.042 | 0.130 | 0.225 | yes |
| continuum | 2.158 | 0.111 | 0.039 | 0.132 | 0.221 | yes |

- The Lean bounds hold at every point checked.
- In 2D the neutral tail alone, with no use of the charged sector, clears three boxes at every coupling. (At beta 1 it
  would not clear the old 0.244 threshold.)

**4D, saved small tori** (part B; `ONEBOX-CHECK.md` 8-9 data, SU(2) Wilson; statistical errors):

| beta | `L` | `F_e(L^4)` | `F_e(L^3 x 2L)` | loss `l(L)` | neutral excess `phi_0 = 2c_lb` | charged excess `phi_1 = phi_0 - l` |
|---|---|---|---|---|---|---|
| 2.3 | 2 | 0.233 +- 0.020 | 0.832 +- 0.093 | -0.37 +- 0.10 | 2.35 | 2.72 |
| 2.3 | 4 | 0.907 +- 0.178 | 1.98 +- 0.61 | -0.16 +- 0.71 | 1.27 | 1.43 |
| 2.3 | 6 | 2.6 +- 1.8 | 2.4 +- 1.5 | +2.8 +- 3.9 | 0.81 | -2.0 |
| 3.5 | 2 | 0.035 +- 0.005 | 0.149 +- 0.020 | -0.08 +- 0.02 | 3.86 | 3.93 |
| 3.5 | 4 | 0.053 +- 0.014 | 0.254 +- 0.064 | -0.15 +- 0.07 | 1.54 | 1.69 |
| 3.5 | 6 | 0.079 +- 0.030 | 0.191 +- 0.073 | -0.03 +- 0.10 | 1.85 | 1.88 |

What the table says:
- At the 4D hand-over (beta 2.3, `L = 4`, `F_e = 0.91`) the neutral excess is about 1.27, far above 0.366. So the
  one-sided tail bound cannot clear there.
- The measured loss is near 0 (central value negative), because `phi_1` is almost as large.
- **In 4D the join loss is a cancellation between two large tails**, the same excitations in both sectors. In 2D, by
  contrast, the neutral tail is small. This reading is not certified: under the resolution floor 1 nothing here is
  certified.
- At `L = 6` the central `phi_1 < 0` contradicts `joinExcess_nonneg`. The errors there (3.9) make that row uninformative.

**Verdict for 2.1.** A rigorous two-sided bound (Lean). It decides the join loss only where the neutral tail is small,
and the 4D hand-over is not such a place. What 4D needs is a bound on `phi_0 - phi_1`, a comparison of the two sectors'
excitation spectra. No tool in this list supplies one. `joinLoss_unbounded` shows that positivity and the transfer
structure alone cannot.

### 2.2 The reflection identity `2 (Z - Z_tw) = <A o sigma - A, A o sigma - A>` (`SUNTwist.lean`)

What it gives:
- `Z_1 >= 0`, each sector a reflection-positivity norm (`ZFam.elec_nonneg`, Lean, every SU(N)).
- With the Cauchy-Schwarz inequality for the reflection form, each `log Z_e(n)` is convex in the transfer length
  [classical].
- These are the hypotheses of 2.1, nothing more.

Why it gives no bound on the loss:
- It acts on each sector separately and identically.
- The loss is the difference `phi_0 - phi_1` of two such sector quantities. Two log-convex sequences can differ in either
  direction (`joinLoss_unbounded` for one sign; swap the sectors for the other).
- This is the Cartan obstruction of `attempts/positivity/NOTE.md` 4.2 in one more form: an inequality built from
  positivity alone holds for U(1) too, and cannot see which sector carries the larger tail.

**Gives: a sign for each sector's excess. For the join loss: nothing** [Lean for the inputs; the "nothing" is
`joinLoss_unbounded`, Lean].

### 2.3 Reflection positivity and chessboard estimates (Froehlich-Israel-Lieb-Simon)

- **In the series direction** a chessboard estimate with two tiles reduces to Cauchy-Schwarz in the reflection form:
  `Z_e(a + b)^2 <= Z_e(2a) Z_e(2b)`. That is log-convexity again, so it adds nothing to 2.1.
- **In the transverse directions** it bounds a twist sheet over a larger cross-section by products over tiles. That is
  parallel composition (twist ratios multiply, `xor_product`), not the series join. By the half-turn, parallel twists
  are the `(+)`-composition of electric factors (`elec_mul`), but that concerns doubling the cross-section, where `F_e`
  drops by about `log 2` (the flux can sit in either half). It is not the join loss.
- What chessboard estimates do well is remove the outside (S2 of `OPEN-STEPS-DMP.md`), at the price of a global free
  energy and reflection-symmetric states.

**Gives: nothing for the join loss** [classical, recalled].

### 2.4 Tomboulis-Yaffe (CMP 100, 1985)

What it is:
- An upper bound of the Wilson loop by a function of the twist (vortex) free energy on the torus, by reflection
  positivity and a chessboard tiling of the loop's surface into cross-section-sized tiles [recalled; the bound's exact
  form is to be read in the paper, or in Kanazawa, arXiv:0808.3442, Theorem 1, which restates it].
- In the language here, the tiling composes per-tile costs into an area law **without loss**.

What it gives for the join loss:
- Nothing directly. Its output is a Wilson loop, not `F_e` of a longer box, and its input is the per-tile twist ratio on
  the torus, an O1-type number.

Reading:
- A lossless series composition exists for the Wilson loop on the torus. That is the same phenomenon as section 2.6,
  where losslessness comes from the twist acting as a symmetry.
- Whether the tube chain could be run on Tomboulis-Yaffe tile costs instead of `F_e` is a separate question; not pursued.

**Gives: nothing for the join loss** [external, recalled; audit item].

### 2.5 Birkhoff-Hopf projective contraction

- Use the pointwise form of 2.6: the slab kernel `K(x, y)` between end faces, and the twist cost
  `log(K(x,y)/K(x, Omega y)) <= Delta(K)`, where `Delta(K)` is the projective diameter of the columns of `K`.
- Birkhoff-Hopf gives `Delta(K_a K_b) <= tanh(Delta(K_a)/4) Delta(K_b)`. So the boundary-uniform twist cost contracts
  geometrically along the series, which is better than additive [classical].
- The input is the **full** diameter: all pairs of end faces, not only `y` against `Omega y`. For the Wilson kernel it
  grows like `beta` times the number of face plaquettes. It is finite on every finite lattice and infinite in the
  continuum.
- Rigorous regime: strong coupling in tick units, or long slabs at a fixed cross-section (Perron-Frobenius slack per
  torus, as in `GRH-LENS.md` 6.5).

**Gives: a contraction of the uniform twist cost, rigorous only where the full diameter is small. Not uniform at fixed
physical size** [classical].

### 2.6 New: in the boundary-uniform form the join loss is zero (Lean, `JoinLossSlab.lean`)

**Setting:**
- A slab between two end faces has kernel `K(x, y) > 0`; its outside is the end-face data `x, y`.
- The centre twist `Omega` of a face multiplies the `k`-links at `x_k = c` by -1; it is an involution.
- The twisted slab is `K(x, Omega y)`.
- Sectors at the far face: `Z_{e=0} = sec0 K = (K(x,y) + K(x, Omega y))/2` and `Z_{e=1} = sec1 K = (K(x,y) - K(x, Omega y))/2`.
- Joining two slabs is `(K_a K_b)(x, y) = sum_z K_a(x, z) K_b(z, y)`.

| result | statement | mark |
|---|---|---|
| `kcomp_sectors` | if `K_b(Omega z, Omega y) = K_b(z, y)`, then `sec_e(K_a K_b) = sum_z sec_e K_a . sec_e K_b`: the mixed terms cancel over the shared face | Lean |
| **`elec_submul`** | pointwise `abs(sec1) <= rho sec0` for both slabs gives `abs(sec1(K_a K_b)) <= rho_a rho_b sec0(K_a K_b)`: **the boundary-uniform electric factor is submultiplicative, join loss 0** | Lean |
| `sector_of_twist` | pointwise twist ratio `K(x, Omega y) >= c K(x, y)` for all end faces gives `abs(sec1) <= elec(c) sec0` | Lean |
| **`three_slabs_O1`** | three slabs, the last two centre-symmetric, each with pointwise twist ratio `>= sqrt 2 - 1`: `mu abs(Z_{e=1}) <= Z_{e=0}` for every end-face outside and every `mu <= 14` (O1 in sector form, via `three_steps_clear`) | Lean |
| `kchain_elec` | `n + 1` such layers: `abs(Z_{e=1}) <= elec(c)^{n+1} Z_{e=0}` | Lean |
| **`kchain_tanh`** | a single-layer floor `K(x, Omega y) >= e^{-2s} K(x, y)` gives `abs(Z_{e=1}) <= tanh(s)^{n+1} Z_{e=0}` | Lean |

**Why the cancellation happens** [Lean for the algebra]:
- If the second slab commutes with the twist, the even part of the first slab's far face meets only the even part of the
  second's near face, and the odd part only the odd part.
- So the joined slab's charged sector is a face sum of products of the two charged sectors. Its absolute value is at most
  the product of the pointwise ratios times the neutral sum.
- On the torus (section 2.1) the trace mixes in each sector's whole spectrum; pointwise, the ratio bound is applied face
  configuration by face configuration and nothing is left over.
- **So the torus join loss comes from annealing. The boundary-uniform quantity, which is the one O1 asks for ("for every
  outside"), composes without loss.**

**When the symmetry holds** [classical lattice fact, not formalised for the gauge chain]:
- Multiplying all `k`-links at `x_k = c` (faces and interior) by -1 leaves every Wilson plaquette invariant: each
  plaquette contains zero or two such links.
- So the slab is centre-symmetric when the two directions transverse to the twist plane are periodic, i.e. when the
  outside is only the two end faces (the **slab geometry**).
- With fixed side outsides, the plaquettes at the side collar that contain one interior and one outside such link
  change sign. Then `K_b(Omega z, Omega y)` is the slab with a **seam** of the twist sheet along its side, not `K_b(z, y)`.
- The join loss in a genuine box is therefore the cost of moving the sheet past the side outside, a two-box quantity of
  the same kind as before. **open**

**The single-layer floor** (`kchain_tanh`):
- For the SU(2) Wilson weight `exp(beta (1/2) tr U_p)`, flipping the `N` plaquettes of a sheet changes each
  configuration's weight by at most `e^{-2 beta N}`. This is the per-configuration floor of `SATURATION.md` 1 (Lean
  there, in its own setting; the bridge to this abstract kernel is not formalised).
- It holds pointwise, so for every end-face outside. With zero join loss, `n` layers have uniform electric factor at most
  `tanh(beta N)^n`: a rate `log coth(beta N)` per layer.
- The electric side `e^{-2 beta N} >= sqrt 2 - 1` holds for `beta N <= log(1 + sqrt 2)/2 = 0.44`, and then three slabs
  clear O1 in slab form (`three_slabs_O1`).
- This is strong coupling in tick units. At fixed physical size `N = (l/a)^2` grows and the rate `~ 2 e^{-2 beta N}`
  vanishes, like plain Doeblin.

**2D check** (`join_loss_check.py` part C, continuum heat kernel on the cylinder; end faces are holonomies, the twist is
`theta -> pi - theta`) [classical formulas; numerical]:
- Submultiplicativity holds at every pair checked, with room: `rho(4+4) = 0.199` against `rho(4)^2 = 0.599`.
- The **uniform hand-over area is 5.99, against 2.16 on the torus (2.8 times larger)**.
- From there, O1 in uniform form needs only 1.47 hand-over areas (8.79), because the uniform cost grows faster than
  additively.

So the uniform form trades the join loss for a harder side. In 2D its O1 area (8.79) is larger than the torus O1 area
(5.08).

---

## 3. The electric side (task 3)

What is known, by form of the side:

| form of the side | what is known | mark |
|---|---|---|
| `0 < c < 1` per finite lattice, every SU(N) | `sunTwistRatio_mem` | Lean |
| one side or the other at every box: `max(F_e, F_tw) >= 0.881` | `log_one_add_sqrt_two_le_max` | Lean |
| torus, any `beta`, fixed cross-section, long enough in the series direction | `c -> 1`: the unique neutral ground state (Perron-Frobenius, strict `Z_tw < Z`) puts the charged sector strictly lower, so `F_e(n) >= n Delta E - const`. Not cubic: the length needed grows with the cross-section | classical |
| pointwise uniform, strong coupling in tick units | twist ratio `>= e^{-2 beta N}` for every outside (`SATURATION.md` 1), so the side holds for `beta N <= 0.44` | Lean (floor, own setting) |
| torus, cubic, beta 2.3 | `L = 4`: `F_e = 0.91` (at the hand-over); `L = 6`: `F_e = 2.6 +- 1.8` (electric centrally, not certified) | numerical |
| strong coupling, convergent expansion | the twist free energy decays (Muenster 1981) | recalled |
| **cubic, uniformly over outsides (box or slab form), at fixed physical size, all beta** | nothing | **open** |

Why the side is not free:
- The hand-over box `L_h` is where `F_e` crosses 0.881. That such a crossing exists, uniformly over outsides, is the side
  statement: some box of fixed physical size is on the electric side for every outside.
- Small boxes at weak coupling are on the magnetic side (`F_e` 0.035 to 0.23 in the table above), as asymptotic freedom
  says. The crossing to the electric side is confinement's onset, which no known theorem supplies uniformly.
- The slab form of section 2.6 makes the side harder: pointwise over every end face. In 2D that costs a factor 2.8 in
  area.

**Status of the side: open** in every form needed for O1. Rigorous only at strong coupling in tick units, or for long
boxes at fixed cross-section.

---

## 4. CPU check (task 4, refute-only)

- **No new simulation was needed.** The pre-registered small-torus run (`ONEBOX-CHECK.md` 8-9) already holds `F_e` on
  `L^4` and on `L^3 x 2L`, with the doubled direction in the twist plane. So `l(L) = 2 F_e(L^4) - F_e(L^3 x 2L)` is exactly
  the transfer-matrix join loss of two `L^4` boxes.
- Run time: about 2 seconds (part B of `join_loss_check.py`).
- **Rule** (`attempts/RULES.md`, universal floor): error bar = max(statistical, resolution floor). The floor is 1 for a
  log-ratio over extent `L`, as pre-registered in `ONEBOX-CHECK.md` 8.3.
- **Refuted at threshold `theta`** if `l - 1.645 sigma > theta`, for `theta` = 0.366 (three boxes) and 0.538 (four).

| beta | `L` | `l` +- stat | three-box (floor 1) | three-box (stat only) | four-box (floor 1) |
|---|---|---|---|---|---|
| 2.3 | 2 | -0.37 +- 0.10 | not refuted | not refuted | not refuted |
| 2.3 | 4 | -0.16 +- 0.71 | not refuted | not refuted | not refuted |
| 2.3 | 6 | +2.8 +- 3.9 | not refuted | not refuted | not refuted |
| 3.5 | 2 | -0.08 +- 0.02 | not refuted | not refuted | not refuted |
| 3.5 | 4 | -0.15 +- 0.07 | not refuted | not refuted | not refuted |
| 3.5 | 6 | -0.03 +- 0.10 | not refuted | not refuted | not refuted |

- **Verdict: the series route is not refuted at any measured point.** A non-refutation is consistent with the route and
  proves nothing.
- On the weakly coupled side (beta 3.5) the loss is slightly negative on statistics alone, i.e. a gain: nearly free flux
  composes better than additively there.
- **New run: not run.** One beta at `L = 8` (snake on `8^4` and `8^3 x 16`) projects to 5.5 CPU-hours raw: 7.3 h
  central, band 5.0 to 10.5 h (`w2/PROJECTION.md` 8). That is over the 1 CPU-hour limit.

---

## 5. What moved on O1

- **The split is in Lean** (`ymOneBox_of_split`), with the correct per-join threshold 0.366 (three boxes) and 0.538
  (four).
- **On the torus**, the join loss is the neutral remnant tail minus the charged one, rigorously bounded on both sides.
  - 2D: the neutral tail alone clears.
  - 4D small tori: the two tails are large and nearly cancel [numerical]. No structural tool bounds the cancellation
    (`joinLoss_unbounded`).
- **In the boundary-uniform form, the form O1 itself asks for, the join loss is zero in the slab geometry** (Lean). O1
  in slab form then reduces to the uniform electric side alone (`three_slabs_O1`), proved at strong coupling in tick
  units (`kchain_tanh`).
- **Not moved:** the uniform electric side at fixed physical size, and, in the box geometry, the side seam. Both are
  open. O1 is open.

**First construction step for the next round** [reading; proposals, not results]:
1. **Slab form of the tube chain.** Does the tube chain (`ym_instance`) accept slabs with periodic transverse directions
   in place of boxes? If so, the join part of O1 is closed and O1 is the uniform side alone.
2. **Bound the side seam.** In the box geometry, bound the seam by the twist's boundary cost: a sheet ending on the side
   collar, like an 't Hooft loop along the side. Its cost per unit length is the dual string tension, which is small on
   the confining side [reading].
3. **The uniform side.** Ask whether the pointwise twist ratio over end faces can be bounded below from the torus ratio
   plus a boundary-decoupling estimate. This is where the effective-coupling crossover (P4) re-enters.

---

## 6. Status

| item | status |
|---|---|
| `JoinLoss`, `ElectricSide` named; `series_bound`, `three_boxes`, `ymOneBox_of_split`, `ymOneBox_lossless`, `ymOneBox_quarter`, `joinLoss_of_flux` | Lean |
| per-join thresholds 0.366 (3 boxes), 0.538 (4) | Lean (inequalities), numerical (decimals) |
| torus sector form: `joinLoss_eq`, `joinExcess_nonneg`, `joinExcess_le_tail`, `joinLoss_bounds`, tails antitone and geometric, `joinLoss_torus`, `ymOneBox_torus`, `joinLoss_unbounded`, `joinLoss_le_iff_oplus` | Lean |
| boundary-uniform form: `kcomp_sectors`, `elec_submul` (zero join loss), `sector_of_twist`, `three_slabs_O1`, `kchain_elec`, `kchain_tanh` | Lean |
| transfer matrix positive, sectors as power sums; slab centre symmetry with periodic transverse directions; side seam | classical (not formalised for the gauge chain) |
| 2D: Lean bounds hold, neutral tail clears, uniform form submultiplicative, uniform hand-over 2.8x torus | numerical |
| 4D saved tori: loss near 0, large near-cancelling tails, not refuted | numerical, refute-only |
| reflection identity, chessboard: nothing for the join loss | Lean (inputs), classical |
| Tomboulis-Yaffe: lossless for the Wilson loop, nothing for `F_e` | external, recalled |
| Birkhoff-Hopf: contraction of the uniform twist cost at small full diameter | classical |
| electric side, uniformly, at fixed physical size | **open** |
| side seam in the box geometry | **open** |
| O1 | **open** |

## 7. Files

- `docs/mass-gap/formal/ProofPhase/Unified/JoinLoss.lean`: the split; the torus sector form.
- `docs/mass-gap/formal/ProofPhase/Unified/JoinLossSlab.lean`: zero join loss in the boundary-uniform form.
- `docs/unified/joinloss-axioms.sh`, `joinloss-axioms.log`: build, `#print axioms` (42 declarations, standard axioms),
  source grep.
- `docs/unified/join_loss_check.py`, `join_loss_check.log`: parts A (2D tails), B (4D saved data), C (2D uniform form),
  and the projection.

## 8. Literature (recalled, not re-read in this round)

- J. Froehlich, R. Israel, E. Lieb, B. Simon, Phase transitions and reflection positivity I, CMP 62 (1978): chessboard
  estimates.
- K. Osterwalder, E. Seiler, Gauge field theories on a lattice, Ann. Phys. 110 (1978): reflection positivity and the
  positive transfer matrix of the Wilson action.
- E. Tomboulis, L. Yaffe, Finite temperature SU(2) lattice gauge theory, CMP 100 (1985): the Wilson loop bounded by the
  vortex free energy. Restated as the Tomboulis-Yaffe inequality in T. Kanazawa, arXiv:0808.3442.
- G. Birkhoff (1957), E. Hopf (1963): projective contraction of positive maps.
- G. Muenster, Nucl. Phys. B180 (1981): strong-coupling expansion of the vortex free energy.
- D. Levin, Y. Peres, E. Wilmer, Markov chains and mixing times: submultiplicativity of boundary-uniform distances, the
  same mechanism as `elec_submul`, there by coupling.
