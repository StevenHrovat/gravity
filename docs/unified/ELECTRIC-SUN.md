# O1 in its sharpest proved form: the Z_N slab join, the side seam, pressing, and the one open statement

Status: 2026-11-23. Proof-focused round on the Yang-Mills open step O1, after `JOIN-LOSS.md` section 2.6.
**O1 is not proved.** Nothing here proves it in four dimensions at fixed physical size.

Lean: `ProofPhase/Unified/ElectricSUN.lean`, `ProofPhase/Unified/ElectricSUNPress.lean` (81 declarations, standard axioms
only: propext, Classical.choice, Quot.sound; no sorry: `electricsun-axioms.sh`, `electricsun-axioms.log`). Third layer
(refute-only, CPU): `electric_sun_check.py`, `electric_sun_check.log`.
Section 10 (2026-11-24): running outsides and remnants, `ProofPhase/Unified/ElectricSUNRunning.lean` (29 declarations,
`electricsun-running-axioms.sh/.log`), CPU `electric_sun_running_check.py/.log`.

Status marks as in `OPEN-STEPS-DMP.md`: **Lean** (proved in Lean, standard axioms), **classical** (known mathematics,
recalled), **numerical** (measured; refutes or guides, never proves), **reading** (interpretation), **open** (not proved
by anyone).

---

## 0. In plain words

**1. Every SU(N) joins without loss.** The SU(2) result of the last round (the boundary-uniform electric factor of two
slabs multiplies when they are joined) now holds for every SU(N) and for every electric sector. The centre of SU(N) is
`Z_N`. Its N sectors are the Fourier transform of the N twisted slabs. When the second slab commutes with the centre
action (the slab geometry), the sectors never mix across the shared face: each sector of the joined slab is the face sum
of the products of that same sector (Lean, `kjoin_secN`). So the pointwise electric factor of each sector multiplies
(Lean, `elecN_submul`). For `N = 2` this is exactly the earlier `elec_submul` (Lean, `secN_two_one`). Instantiated for
`N = 2, 3, 5, 11` through the general theorem (Lean).

**2. From a twist ratio to a sector factor, for every N.** If every twist changes the slab weight by at most a factor `c`
(pointwise), each nontrivial sector is at most `(N-1)(1-c)/(N-1+c)` times the neutral one (Lean, `sector_of_twistN`).
For SU(2) this is the sharp `(1-c)/(1+c)`. The self-dual point `sqrt 2 - 1` needs a twist ratio of at least
`cstar_N` = 0.414 (N = 2), 0.485 (3), 0.531 (5), 0.562 (11), rising towards `2 - sqrt 2 = 0.586` [Lean for the
inequalities; numerical for the decimals]. For `N >= 3` the bound is valid but not sharp.

**3. Pressing, fine to coarse (Lean).** A slab of thickness `kL` is `k` slabs of thickness `L` joined, so its factor is at
most the `k`-th power (`twistCertN_kpow`): the electric cost adds up exactly along the series. Coarse-graining an end face
(any nonnegative block kernel on the near face, a centre-symmetric one on the far face) never raises the factor
(`twistCertN_left`, `twistCertN_right`). Together: `press`.

**4. O1 is now exactly one named statement plus the seam (Lean).**
- **`HandoverSide`** [open]: at the hand-over slab (fixed physical thickness `L_h`), for every cutoff, every nontrivial
  sector and every end-face outside, the charged sector is at most `sqrt 2 - 1` times the neutral one. This is literally
  O1 at `mu = 1 + sqrt 2` at the single length `L_h` (`handoverSide_iff`).
- In the **slab geometry** it gives O1 at `3 L_h` for every `mu <= 14`, every cutoff, every sector
  (`O1_slab_of_handover`), also after coarse-graining the end faces (`O1_slab_coarse`).
- In a **box** (fixed side outsides) add the **seam**: the exact seam cost `delta` of a layer is how much its weight moves
  when the centre action passes the side collar. Joining a layer with seam cost `delta` carries the factor `u` to
  `(1 + delta) rho u + delta` (Lean, `elecN_seam`): the seam is exactly the transport's fresh uncertainty per join.
  With seam cost at most `1/25` per join, three box layers on the electric side give O1 for every `mu <= 7`
  (`O1_box_of_handover_seam`).

**5. The seam: bounded only where a per-configuration floor is small.** A floor `e^{-s} <= (weight change) <= e^{s}`
gives seam cost `e^s - 1` (Lean, `seamDefect_of_floor`), within budget for `s <= 1/50`. For SU(2) Wilson `s = 2 beta M`
with `M` the seam plaquettes of one layer: strong coupling or a short seam. Reflection positivity, the chessboard estimate
and the transport theorem add no smallness in the pointwise form (section 3). Seam cost exactly zero holds for side
outsides averaged over their centre orbit (`centreSym_ksym`, Lean; the identification is classical).

**6. The CPU check (refute-only).** On tiny SU(2) slabs at beta 2.3 the pointwise electric factor is far above
`sqrt 2 - 1`: the worst end faces are the ordered (cold) ones, where the twist cost follows roughly the classical law
`proportional to beta L/T` (2^3 cross-section: `|log c|` = 11.5, 5.1, 2.9, 2.3 for `T` = 1 to 4, against the needed
0.881). Random end faces sit near the threshold. Details in section 6.

**What O1 now is, exactly.** O1 = `HandoverSide` (one statement, uniform in the cutoff, pointwise over end faces) plus,
in a box, a seam cost at most `1/25` per join. In the slab geometry the seam is absent and O1 = `HandoverSide` alone.
Both pieces are open at fixed physical size. Proved instead: everything around them, for every SU(N).

---

## 1. Setting

`ElectricSUN.lean`, section 1 [Lean, definitions]:
- the centre `Z_N` acts on a finite set of face configurations (`AddAction (ZMod N) Y`): `k +ᵥ y` multiplies the
  `k`-links of the face at `x_k = c` by `omega^k`;
- a slab is a kernel `K x y` between its end faces; `K x (k +ᵥ y)` is the slab with twist `omega^k`;
- **sector `e`**: `secN K e x y = (1/N) sum_k omega^{-ek} K x (k +ᵥ y)`, the `Z_N` transform of `SUNTwistSectors`
  (`secN_eq_elecZ`); the neutral sector `sec0N` is real (`secN_zero`);
- **join**: `kjoin Ka Kb x y = sum_z Ka x z Kb z y` (face spaces may differ, which serves coarse-graining;
  `kjoin = kcomp` of `JoinLossSlab` when they agree);
- **`CentreSym N K`**: `K (k +ᵥ z) (k +ᵥ y) = K z y`;
- **`twistCertN N K e u`**: `|Z_e| <= u Z_0` at every end-face pair (the boundary-uniform factor of sector `e`).

**When is a slab centre-symmetric?** [classical lattice fact, not formalised for the gauge chain] Multiply all
`k`-links at `x_k = c` (faces and interior) by the central element `omega^j`. Each Wilson plaquette contains none of
these links or two, one as `U` and one as `U^+`, and `omega^j` is central, so every plaquette is unchanged. With periodic
transverse directions (the slab geometry) this is a symmetry of the slab kernel. With fixed side outsides the side
outside's own links at `x_k = c` are not transformed, and the collar plaquettes between them and the interior change:
the **seam**. Transforming the side outside as well restores the symmetry, so
`K^omega(k +ᵥ z, k +ᵥ y) = K^{omega'}(z, y)` with `omega'` the side outside moved by the centre action along the seam.

---

## 2. The Z_N slab join (task 1)

| result | statement | mark |
|---|---|---|
| `inner_shift` | the shared-face sum after twisting the first slab's far face by `j` and the second's by `l` is the joined slab twisted by `j + l` (second slab centre-symmetric) | Lean |
| **`kjoin_secN`** | `secN (Ka Kb) e = sum_z secN Ka e . secN Kb e`: **each sector of the join is the face sum of products of the same sector** | Lean |
| `kjoin_sec0N` | the same for the neutral sector | Lean |
| **`elecN_submul`** | `twistCertN Ka e ra`, `twistCertN Kb e rb`, `Kb` centre-symmetric give `twistCertN (Ka Kb) e (ra rb)`: **zero join loss, every sector, every N** | Lean |
| `twistCertN_one` | every nonnegative kernel has factor 1 in every sector (`|omega| = 1`) | Lean |
| **`sector_of_twistN`** | twist ratio `>= c` for every twist and end face gives factor `rhoN N c = (N-1)(1-c)/(N-1+c)` in every sector `e != 0` | Lean |
| `rhoN_two`, `cstarN_two` | `rhoN 2 = elec` (sharp), `cstar_2 = sqrt 2 - 1` | Lean |
| `rhoN_le_of_cstar` | twist ratio `>= cstar_N = (N-1)(2 - sqrt 2)/(N - 2 + sqrt 2)` gives factor `<= sqrt 2 - 1` | Lean |
| `cstarN_chain` | `cstar_2 < cstar_3 < cstar_5 < cstar_11 < 2 - sqrt 2` | Lean |
| **`three_slabsN_O1`** | three slabs, the last two centre-symmetric, sector-`e` factor `<= sqrt 2 - 1` each: `mu |Z_e| <= Z_0` for `mu <= 14` at every end face | Lean |
| `three_slabsN_O1_twist` | the same from twist ratios `>= cstar_N`, every `e != 0` | Lean |
| `kchainN_elec` | `n + 1` centre-symmetric layers with factor `r`: factor `r^{n+1}` | Lean |
| `secN_two_one`, `secN_two_zero`, `omega2_involutive` | for `N = 2` the sectors are `sec1`, `sec0` of `JoinLossSlab` with `Omega = (1 +ᵥ .)`: `elecN_submul` contains `elec_submul` | Lean |
| `su2_slab_O1`, `su3_slab_O1`, `su5_slab_O1`, `su11_slab_O1` | the owner's candidates, each from `three_slabsN_O1_twist` | Lean |

**Why the sectors do not mix** [Lean for the algebra]. Expand both sector transforms over the shared face. The twist `j`
on the first slab's far face can be moved through the face sum onto the second slab, because the second slab commutes
with the centre action. It then adds to the second slab's own twist `l`. The double sum over `(j, l)` with character
`omega^{-e(j+l)}` collapses to a single sum over `j + l`, which is the sector-`e` transform of the joined slab. No
cross term between different sectors survives, for every `N`: the Fourier transform diagonalises the join.

**The twist-to-sector bound** [Lean]. With `a_k = K x (k +ᵥ y)` and `m` the smallest of them: the nontrivial character
sums to zero, so `|N Z_e| = |sum_k omega^{-ek}(a_k - m)| <= sum_k (a_k - m)`, i.e. `|Z_e| <= Z_0 - m`. The twist ratio
gives `c a_j <= m` for every `j`, so `c sum_k a_k <= (N - 1 + c) m`. Combining gives `rhoN`. For `N = 2` the two values
are `m` and the other, and the bound is attained; for `N >= 3` the extreme configurations are not all simultaneously
attainable, so the bound is valid, not sharp [classical arithmetic].

**Thresholds** [Lean inequalities; decimals in `electric_sun_check.log` part A]:

| N | `cstar_N` | meaning |
|---|---|---|
| 2 | 0.4142 | `= sqrt 2 - 1`, as before |
| 3 | 0.4853 | |
| 5 | 0.5308 | |
| 11 | 0.5625 | |
| large | `-> 2 - sqrt 2 = 0.5858` | |

O1 for SU(N) in sector form is one condition per nontrivial sector (as `SUN-PRIMES.md` says). Through the `Z_N` join each
sector composes by itself; nothing ties the sectors together.

---

## 3. The side seam (task 2)

### 3.1 The exact seam cost (Lean)

`ElectricSUNPress.lean`, section 3.

| result | statement | mark |
|---|---|---|
| **`SeamDefect N K delta`** | `|K(k +ᵥ z, k +ᵥ y) - K(z, y)| <= delta K(z, y)` for every twist and end-face pair: **the exact seam cost of a layer** | definition |
| `seamDefect_zero_iff` | seam cost 0 is `CentreSym` | Lean |
| `ksym`, `centreSym_ksym` | the centre average `(1/N) sum_j K(j +ᵥ z, j +ᵥ y)` is centre-symmetric | Lean |
| `twistCertN_ksym` | the centre average keeps every sector factor | Lean |
| `ksym_sub_le`, `ksym_le` | a layer is within `delta` of its centre average | Lean |
| **`elecN_seam`** | factors `ra`, `rb`, seam cost `delta` of the added layer: factor of the join `<= (1 + delta) ra rb + delta` | Lean |
| `seamTransportN` | the box chain is a `TransportsCert` with factor `(1 + delta) rho` and fresh uncertainty `r = delta` per join | Lean |
| `ym_box_bridge` | O1 at `mu` after `n` joins once `mu (theta'^n u_0 + delta/(1 - theta')) <= 1`, `theta' = (1 + delta) rho < 1` | Lean |
| `threeBox`, **`three_boxes_seam`** | three layers at factor `theta`, seam cost `delta`: transported value `(1+delta)((1+delta) theta^2 + delta) theta + delta` | Lean |
| `three_boxes_seam_num` | `theta = sqrt 2 - 1`, `delta <= 1/25`: O1 for every `mu <= 7` (`threeBox = 0.134`; `mu_4 = 6.77`) | Lean |
| `seamDefect_of_floor`, `seamDefect_small` | a per-configuration floor `e^{-s} <= ratio <= e^{s}` gives `delta <= e^s - 1 <= 1/25` for `0 <= s <= 1/50` | Lean |
| `O1_box_of_floors` | twist floor `>= cstar_N` for every layer and seam floor `s <= 1/50`: O1 for `mu <= 7` | Lean |

**This is the fresh uncertainty `r_n` of `Transport.lean`, exactly.** The proof of `elecN_seam` splits the added layer
into its centre average (which joins with zero loss and keeps the layer's factor) and the remainder (at most `delta` times
the layer). The remainder contributes at most `delta Z_0` to every sector; the centre average inflates the neutral weight
by at most `1 + delta`. So the seam enters the transport as `r = delta` per join, with the factor raised to
`(1 + delta) rho`. `TRANSPORT.md` 3.1 named `SeamTransport` with an unspecified `sigma`; here `sigma = delta` and the
factor correction `(1 + delta)` are derived, not assumed.

**Seam budget** [Lean for 1/25 at `mu <= 7`; the rest arithmetic, `electric_sun_check.log` part A]:

| seam cost per join `delta` | 0 | 0.01 | 0.02 | 0.04 | 0.05 | 0.10 |
|---|---|---|---|---|---|---|
| three boxes clear O1 for `mu <=` | 14.07 | 11.54 | 9.77 | 7.46 | 6.66 | 4.32 |

### 3.2 What the tools give for the seam

The seam cost is a **pointwise** quantity: a supremum over end-face pairs and over side outsides of the relative change
of a layer's weight when the centre action moves past the side collar. Equivalently [classical identification, section
1], the relative change when the side outside is moved by the centre action along the seam line: `M` collar plaquettes
per layer (about the cross-section's perimeter times the layer thickness, in lattice units).

1. **Per-configuration floor** (the only pointwise tool that bounds a size) [Lean in abstract form; the SU(2) floor is
   classical]. Each seam plaquette changes the SU(2) Wilson weight by a factor in `[e^{-2 beta}, e^{2 beta}]`, so a layer's
   weight moves by at most `e^{2 beta M}`: `delta <= e^{2 beta M} - 1`. Within the budget `1/25` for `beta M <= 1/100`
   (`seamDefect_small`). **This is a bound in a regime: strong coupling in tick units, or a short seam (small
   cross-section, thin layer).** For SU(N), `s = beta_N M |omega^k - 1|` in the normalisation `exp((beta_N/N) Re tr U)`
   [classical].
2. **Reflection positivity across the side faces.** It needs a reflection-symmetric measure: a reflection maps the box
   with side outside `omega` onto a box with the reflected outside, and the positivity statements concern expectations
   `<theta(F) F> >= 0` in the doubled, symmetric system. What it gives for the seam:
   - a sign structure: the seam's effect on the twist sector is a difference of reflection-positive forms (the same
     identity that proves `0 < c < 1` in `SUNTwist.lean`);
   - Cauchy-Schwarz: a partition function with different outsides on the two sides of a reflection plane is bounded
     by the geometric mean of the ones with reflection-symmetric outsides.

   It moves the question to symmetric outsides; it does not make the cost small. **Gives: sign and symmetrisation, no
   size** [classical].
3. **Chessboard estimate.** It bounds a product of local observables on a torus by their disseminated versions. Two
   obstructions in the pointwise form: the box is not a torus (fixed side outsides break the reflections), and the
   sup over end faces is not an expectation. On the torus the chessboard bound of the seam observable is the free energy
   of a twist sheet disseminated over the torus, an annealed (O1-type) number again. **Gives: an annealed bound, nothing
   pointwise** [classical].
4. **Transport theorem.** It composes the seam exactly (`seamTransportN`, `ym_box_bridge`): bounded transport with fresh
   uncertainty `delta` per join, budget `1/25` for three boxes at `mu <= 7`, relaxing towards `delta < (1 - theta')/mu`
   with many layers (at the price of length). **Gives: the budget, not the bound** [Lean].

**Why no bound at fixed physical size is reachable with these tools** [reading, with one classical input]:
- The floor bound grows like `e^{2 beta M}`. At fixed physical size `M ~ (L_h/a)^2` grows as the lattice spacing `a`
  shrinks, and `beta` grows too: the bound degenerates, like plain Doeblin.
- The expected true size of the seam cost is the free energy of the line where the twist sheet meets the fixed side
  outside: a perimeter-type cost of an 't Hooft line, proportional to the seam length in lattice units with a
  UV-sensitive coefficient [reading]. In the pointwise sup form nothing renormalises it away, so even the true value need
  not be small uniformly in the cutoff.
- Reflection positivity and chessboard estimates are blind to sizes in the pointwise form: they need reflection-symmetric
  or annealed boundary data, and the seam cost is a sup over arbitrary fixed data.

**Two ways around the seam, both exact** [Lean for the algebra]:
- the **slab geometry** (periodic transverse directions): seam cost 0 (`seamDefect_zero_iff`, `seamTransport_slab`);
- **centre-orbit-averaged side outsides**: replacing a pure side outside by the average over its centre orbit makes the
  layer exactly `ksym`, which is centre-symmetric (`centreSym_ksym`). For a pure side outside the seam is precisely the
  deviation from its orbit average (`ksym_sub_le`). Whether the tube chain can work with orbit-averaged sides is the same
  question as whether it accepts slabs (`JOIN-LOSS.md` 5, step 1) [open].

---

## 4. Pressing, fine to coarse (task 3)

`ElectricSUNPress.lean`, sections 1 and 2.

| result | statement | mark |
|---|---|---|
| `secN_kjoin_left`, `sec0N_kjoin_left` | joining on the near face is linear in the sectors (no symmetry needed) | Lean |
| `twistCertN_left` | coarse-graining the near face with any `P >= 0` keeps the factor | Lean |
| `twistCertN_right` | coarse-graining the far face with a centre-symmetric `Q >= 0` keeps the factor | Lean |
| `coarse`, `twistCertN_coarse` | both faces | Lean |
| `centreSym_kjoin`, `centreSym_coarse`, `centreSym_kpow` | joins and centre-symmetric coarse-grainings stay centre-symmetric, so pressing can be iterated | Lean |
| `kpow`, `twistCertN_kpow` | thickness `(n+1) L` = `n + 1` copies of thickness `L`: factor `u^{n+1}` | Lean |
| **`press`** | coarse-grained slab of thickness `(n+1) L`: factor `<= u^{n+1}` | Lean |
| `press_cost`, `elecCost_mul` | in cost form `-log u`: costs add along the series exactly | Lean |

**The composition law.** `F(kL) >= k F(L)` for the boundary-uniform electric cost `F = -log u`, with no loss term; coarse-graining the end faces only raises `F`. This is the pointwise counterpart of
`flux_superadd_iter`, which on the torus carries a loss `2C` per join; in the pointwise form the loss is 0 [Lean].

**The exact remaining hypothesis** [Lean, named]:
- **`HandoverSide N Kh`**: `forall i, forall e != 0, twistCertN N (Kh i) e (sqrt 2 - 1)`, with `Kh i` the hand-over slab
  (fixed physical thickness `L_h`) at cutoff `i`, any side outside folded into the index. **open**
- `handoverSide_iff`: it is O1 at `mu = 1 + sqrt 2` at the single length `L_h`.
- `handoverSide_of_twist`: it follows from a pointwise twist ratio `>= cstar_N` at the hand-over slab, every cutoff.
- `O1_slab_of_handover`: slab geometry, `HandoverSide` gives O1 at `3 L_h` for every `mu <= 14`, every cutoff, every
  nontrivial sector, every end face. `O1_slab_coarse`: also after coarse-graining the end faces.
- `O1_box_of_handover_seam`: box geometry, `HandoverSide` for the three layers plus seam cost `<= 1/25` per join give O1
  at `3 L_h` for every `mu <= 7`.

**So O1 = `HandoverSide` + seam (box), or `HandoverSide` alone (slab), as Lean statements.** Nothing else is assumed.

---

## 5. What is open, exactly

| piece | form | status |
|---|---|---|
| `HandoverSide` | pointwise over end faces, uniform in the cutoff, at a fixed physical thickness | **open** |
| seam cost `<= 1/25` per join | pointwise over end faces and side outsides, uniform in the cutoff | **open** (proved only for `2 beta M <= 1/50`) |
| slab geometry or orbit-averaged sides accepted by the tube chain | removes the seam | **open** |
| lattice facts: transfer kernel composes; centre symmetry with periodic transverse directions; seam = side collar | | classical, not formalised for the gauge chain |

**What `HandoverSide` asks, in plain terms.** Some slab of fixed physical thickness must be on the electric side for
every pair of end faces, including the ordered (cold) ones, at every lattice spacing. Section 6 shows that on tiny slabs
the ordered faces are the worst by far. The continuum version of the cold-face twist cost is a classical-action-type
quantity, controlled by the running coupling at scale `L_h` [reading]; whether it reaches `|log c| <= log(1 + sqrt 2)`
at some fixed `L_h` is the confinement-onset question in its sharpest form.

---

## 6. CPU check (task 4, refute-only)

`electric_sun_check.py`, `.log`. SU(2) Wilson action, beta 2.3. Slab: spatial `2^3` periodic (slab geometry), `T`
temporal layers between two fixed end faces `x` (slice 0) and `y` (slice `T`). The twist flips `y`'s 0-links at `s_0 = 0`:
`M = 4` sheet plaquettes. For each end-face pair the twist ratio `c(x, y) = K(x, Omega y)/K(x, y)` is measured by
thermodynamic integration in the sheet coupling (heat bath, Gauss-Legendre in the twist strength), and the pointwise
factor is `rho = |1 - c|/(1 + c) = tanh(|log c|/2)`. The worst found is a **lower bound** on the boundary-uniform factor.

Run time 2096 s (35 CPU-minutes, single process), under the 1 CPU-hour limit; timed first with a 4-minute quick
run (`--quick`). Statistical errors on `log c` from 10 blocks; the heat bath was checked against the exact
single-link mean `I_2(k)/I_1(k)`.

**Part B, `1^3 x 1`, exact** [classical, arithmetic]: with centre-element end faces the sheet plaquette does not depend
on the interior link, so the floor is attained: worst twist ratio `e^{-2 beta} = 0.010`, pointwise factor
`tanh(beta) = 0.980`.

**Part C, `2^3 x T`** [numerical]. Worst `rho` over each set of end-face pairs:

| `T` | ordered faces (16) | near-ordered (16) | identical random faces (16) | independent random faces (32) |
|---|---|---|---|---|
| 1 | `log c = -11.47 +- 0.09`, `rho = 1.000` | `-10.25`, 1.000 | `-10.60`, 1.000 | `-2.44`, 0.839 |
| 2 | `-5.12 +- 0.11`, 0.988 | `-4.62`, 0.980 | `-1.93`, 0.747 | `+1.18`, 0.528 |
| 3 | `-2.92 +- 0.14`, 0.897 | | `-1.14`, 0.514 | |
| 4 | `-2.26 +- 0.20`, 0.811 | | | |

The pointwise side needs `rho <= sqrt 2 - 1 = 0.414`, i.e. `|log c| <= log(1 + sqrt 2) = 0.881`.

**What it says:**
- **The pointwise side fails on every slab measured, by far.** Refuted at 1.645 sigma on statistics alone for
  `T = 1, 2, 3, 4`; with the project's resolution floor 1 on a log-ratio it is still refuted for `T = 1, 2, 3`
  (`|log c| - 1.645 = 9.8, 3.5, 1.3 > 0.881`), not for `T = 4` (`0.61`). These slabs are tiny and at beta 2.3 they are on
  the magnetic side, as expected; this does not refute `HandoverSide`, which concerns a slab of fixed physical size.
- **The ordered (cold) end faces are the worst by far.** Random end faces are near the threshold already at `T = 2`;
  the ordered ones cost 3 to 5 times more. So the pointwise side is much harder than a typical-boundary side, which is
  exactly the gap between `HandoverSide` and the annealed (torus) side.
- **The cold-face twist cost falls with thickness:** 11.5, 5.1, 2.9, 2.3 for `T = 1, ..., 4`. The first step is close to
  the classical `beta L/T` law of a twist forced between two cold faces (about `2.5 beta L/T` here); later steps fall a
  little faster, as the small cross-section starts to gap the transfer matrix [numerical; the law is a reading].
  Extrapolation to `0.881` is not attempted: it is outside the measured range and a tiny cross-section is not the
  hand-over geometry.
- **Floor versus truth:** the floor `e^{-2 beta M} = e^{-18.4}` is far below the measured cold-face ratio already at
  `T = 1` (`e^{-11.5}`); the per-configuration floor is attained only in the degenerate `1^3 x 1` slab.

**Not run:** larger cross-sections (`4^3`) would multiply the run time by about 8 per slab and exceed the limit.

---

## 7. Status

| item | status |
|---|---|
| `kjoin_secN`, `elecN_submul`: zero join loss for every SU(N), every sector | Lean |
| `sector_of_twistN`, `rhoN_two`, `cstarN_*`, `three_slabsN_O1(_twist)`, `kchainN_elec`, `secN_two_*`, instances `N = 2, 3, 5, 11` | Lean |
| pressing: `press`, `twistCertN_kpow`, `twistCertN_left/right/coarse`, `centreSym_*`, `press_cost` | Lean |
| `HandoverSide` named; `handoverSide_iff`, `handoverSide_of_twist`, `O1_slab_of_handover`, `O1_slab_coarse` | Lean (statements around the open piece) |
| seam: `SeamDefect`, `ksym`, `elecN_seam`, `seamTransportN`, `ym_box_bridge`, `three_boxes_seam(_num)`, `seamDefect_of_floor/small`, `O1_box_of_handover_seam`, `O1_box_of_floors` | Lean |
| seam bound in a regime (`2 beta M <= 1/50`) | Lean (abstract) + classical (SU(2) floor) |
| RP, chessboard for the seam: sign and symmetrisation, annealed only | classical |
| tiny-slab pointwise factor at beta 2.3: far above `sqrt 2 - 1`; ordered faces worst | numerical, refute-only |
| `HandoverSide` | **open** |
| seam cost `<= 1/25` uniformly in the cutoff | **open** |
| O1 | **open** |

## 8. Files

- `docs/mass-gap/formal/ProofPhase/Unified/ElectricSUN.lean`: the `Z_N` slab join, twist-to-sector bound, three slabs,
  chains, `N = 2` bridge, instances.
- `docs/mass-gap/formal/ProofPhase/Unified/ElectricSUNPress.lean`: pressing, coarse-graining, `HandoverSide`, the seam,
  the box bridge, O1 as named statement plus seam.
- `docs/unified/electricsun-axioms.sh`, `electricsun-axioms.log`: build, `#print axioms` on 81 declarations, source grep.
- `docs/unified/electric_sun_check.py`, `electric_sun_check.log`: parts A (thresholds, budgets), B (exact `1^3 x 1`),
  C (Monte Carlo, `2^3 x T`).

Not yet added to any aggregate import or to the theorem gate list (the coordinator's step).

## 9. Literature (recalled, not re-read in this round)

- G. 't Hooft, A property of electric and magnetic flux in non-Abelian gauge theories, Nucl. Phys. B153 (1979): the
  `Z_N` electric sectors as the Fourier transform of twisted boxes.
- K. Osterwalder, E. Seiler, Ann. Phys. 110 (1978): reflection positivity of the Wilson action.
- J. Froehlich, R. Israel, E. Lieb, B. Simon, CMP 62 (1978): chessboard estimates.
- M. Creutz, Phys. Rev. D21 (1980): the SU(2) heat bath used in part C.

---

## 10. Running outsides and remnants (next step, 2026-11-24)

Lean: `ProofPhase/Unified/ElectricSUNRunning.lean` (29 declarations, standard axioms only, no sorry:
`electricsun-running-axioms.sh`, `.log`). CPU (refute-only): `electric_sun_running_check.py`, `.log`.

**Why.** Section 6 showed that frozen (ordered, cold) end faces dominate the pointwise side. A twist forced between two
frozen faces at fixed physical shape costs about `(1/g^2) L/T` classically, which grows without bound in the continuum,
so `HandoverSide` over *all* end faces is most likely false there [reading on numerical data]. The owner's answer
(`PREP.md`, last entry): "Frozen faces aren't running outsides, so they don't count, but their ticks of not counting do
count as remnants." This section builds that reformulation.

### 10.1 In plain words

- **Running outsides.** The electric side is asked only for end-face pairs in a running set `R`: faces typical of the
  measure, for example faces whose own action density lies in a typical window (`windowFaces`). Frozen faces are left
  out of the quantifier.
- **Remnant.** When two slabs are joined, the shared face is integrated over. Where it is not running, the sector is
  bounded by the trivial factor 1 (every factor is at most 1: `0 < c < 1` for every SU(N)). So the frozen shared faces
  contribute at most their weight. If that weight is at most the fraction `epsilon` of the joined neutral weight
  (`RemnantMass`), the remnant adds at most `epsilon` per join.
- **The remnant is a fresh uncertainty of the transport theorem** (Lean): in a slab the chain carries the running
  factor with factor `rho` and fresh uncertainty `r = epsilon` per join; in a box with seam cost `delta`, factor
  `(1 + delta) rho` and `r = (1 + delta) epsilon + delta`.
- **O1 assembly** (Lean): O1 over running outsides = `HandoverSideRunning` + remnant + seam, with explicit thresholds:
  slab `epsilon <= 1/20` per join, box `epsilon, delta <= 1/50` per join, each giving O1 for every `mu <= 7`.
- **CPU, refute-only:** on typical (thermalised) end faces of tiny slabs (beta 2.3, `2^3 x T`) the median pointwise
  factor is 0.60 (`T = 2`) and 0.46 (`T = 3`) against 0.414, but about 60% of typical pairs miss the side and the worst
  typical pair is nearly as bad as a frozen one. A running set defined by the action density alone is too wide there
  (section 10.4).

### 10.2 Lean

| result | statement | mark |
|---|---|---|
| `twistCertOn N K R e u` | `|Z_e| <= u Z_0` for the end-face pairs in `R` only | definition |
| `DiagInvariant N R` | `R` invariant under the centre action on both faces | definition |
| **`RemnantMass N Ka Kb Ra Rb Rab epsilon`** | for every running outer pair of the join, the shared faces that are not running carry at most `epsilon` of the joined neutral weight | definition (the instantiable hypothesis) |
| `runPairs`, `windowFaces`, `windowFaces_invariant`, `diagInvariant_runPairs` | running pairs = both faces running; a window of a centre-invariant face density is centre-invariant | Lean |
| `remnant_of_faces` | the remnant from face-level running sets: for running outer faces, the non-running shared faces carry at most `epsilon` | Lean |
| `twistCertOn_ksym`, `sec0N_ksym_le` | the centre average keeps a running factor; its neutral weight is within `1 + delta` | Lean |
| **`elecN_running`** | box: running factors `ra`, `rb`, remnant `epsilon`, seam `delta`: join factor `(1 + delta)(ra rb + epsilon) + delta` on the running outer pairs | Lean |
| `elecN_running_slab` | slab: `ra rb + epsilon` | Lean |
| **`runningTransport_slab`** | the slab chain over running sets is a `TransportsCert` with factor `rho` and **fresh uncertainty `r = epsilon`** | Lean |
| `runningTransport` | box: factor `(1 + delta) rho`, `r = (1 + delta) epsilon + delta` | Lean |
| `ym_running_bridge` | O1 on the running pairs after `n` joins once `mu (theta'^n u_0 + r/(1 - theta')) <= 1` | Lean |
| `three_slabs_running`, `three_slabs_running_num` | three slabs: transported value `theta^3 + (1 + theta) epsilon`; `epsilon <= 1/20` gives O1 for `mu <= 7` | Lean |
| `three_boxes_running`, `three_boxes_running_num` | three boxes: `epsilon, delta <= 1/50` give O1 for `mu <= 7` (`threeBoxRun = 0.131`) | Lean |
| **`HandoverSideRunning N Kh R`** | the pointwise electric side at the hand-over slab, every cutoff, every `e != 0`, running pairs only | named, **open** |
| `handoverSideRunning_of_handoverSide` | the all-outsides side implies the running one | Lean |
| **`O1_slab_running`**, **`O1_box_running`** | O1 at `3 L_h` on running pairs, every cutoff, every sector, from `HandoverSideRunning` + remnant (+ seam) | Lean |

**What the remnant means as a probability** [Lean for the algebra; the reading of the weights is classical]. In the slab
geometry the neutral sector of a join is `sum_z Z_0^a(x, z) Z_0^b(z, y)` (`kjoin_sec0N`), so
`Z_0^a(x, z) Z_0^b(z, y) / Z_0^{ab}(x, y)` is the neutral-sector conditional law of the shared face given the outer
faces. `RemnantMass` with `epsilon` says: given running outer faces, the shared face is not running with conditional
probability at most `epsilon`. Through `remnant_of_faces` this is a statement about one face: its action density leaves
the typical window with conditional probability at most `epsilon`, a large-deviation estimate of a boundary average.

**Thresholds** [Lean for the stated ones; arithmetic for the rest]:

| geometry | O1 for `mu <= 7` needs | exact boundary |
|---|---|---|
| slab, remnant only | `epsilon <= 1/20` | `epsilon <= (1/mu - theta^3)/(1 + theta) = 0.0508` at `mu = 7` |
| box, remnant and seam | `epsilon <= 1/50` and `delta <= 1/50` | e.g. `epsilon = delta = 1/40` already fails (`7 x 0.1468 > 1`) |
| slab, `mu <= 14` | `epsilon <= 2.5 x 10^-4` | the self-dual cube `theta^3 = 0.0711` leaves almost no room at `mu = 14` |

**The conclusion is O1 over running outsides.** `O1_slab_running` and `O1_box_running` give `mu |Z_e| <= Z_0` for running
outer pairs, not for frozen ones. Whether the tube chain is satisfied by O1 over running outsides (its outsides being
themselves typical, by the same remnant argument one level up) is the next consistency question [open].

### 10.3 What is open now

| piece | status |
|---|---|
| `HandoverSideRunning`: pointwise side for running end faces, uniform in the cutoff | **open** |
| remnant `epsilon <= 1/20` (slab) / `1/50` (box) per join, uniform in the cutoff: a large-deviation bound for the face action density under the conditional measure | **open** |
| seam `delta <= 1/50` (box) | **open** (proved only under the per-configuration floor) |
| the tube chain accepts O1 over running outsides | **open** |

Compared with section 5 the open statement is weaker (frozen faces are no longer quantified over), at the price of one
more named quantity, `epsilon`, which is a probability and so the natural object for a large-deviation estimate.

### 10.4 CPU check: typical end faces only (refute-only)

`electric_sun_running_check.py`, `.log`. Same slab and measurement as section 6 (SU(2), beta 2.3, `2^3 x T`), but the
end-face pairs are drawn from the Wilson measure itself: slices 3 and `3 + T` of a thermalised `2^3 x (T + 6)` slab
(150 heat-bath sweeps), 64 pairs per `T`. Run time 723 s (12 CPU-minutes), timed first with a 2.5-minute quick run;
under the 30 CPU-minute limit. [numerical]

| | `T = 2` | `T = 3` |
|---|---|---|
| face action density `(1/2) tr P` (typical window) | mean 0.645, range 0.43 to 0.82 | mean 0.629, range 0.32 to 0.81 |
| `log c`: mean, spread over pairs | -1.26, 1.53 | -0.55, 1.12 |
| `rho` over typical pairs: median / 75% / 90% | 0.599 / 0.861 / 0.924 | 0.456 / 0.615 / 0.737 |
| worst typical pair | `rho = 0.953` (`log c = -3.73 +- 0.13`) | `rho = 0.858` (`log c = -2.57 +- 0.14`) |
| fraction of typical pairs with `rho <= sqrt 2 - 1 = 0.414` | 0.33 | 0.42 |
| pairs significantly off the side (1.645 sigma, statistics only) | 37 of 64 | 26 of 64 |
| for comparison: worst ordered (frozen) pair, section 6 | `log c = -5.12` | `log c = -2.92` |

**How far from `sqrt 2 - 1`:**
- Over typical faces the median factor is 0.60 at `T = 2` and 0.46 at `T = 3`, against 0.414: the typical pair is close
  to the electric side at `T = 3` and moving towards it with thickness.
- The worst typical pairs are still far off: `|log c| = 3.7` and `2.6` against the needed 0.881. Refuted at 1.645 sigma
  on statistics and, with the resolution floor 1, still refuted (`3.73 - 1.645 = 2.1`, `2.57 - 1.645 = 0.93 > 0.881`).
- **So "typical" in the sense of the measure (the faces' own sample, with action density in the window 0.3 to 0.8) does
  not make the pointwise side hold on these tiny slabs at beta 2.3.** About 60% of typical pairs miss it. The
  `HandoverSideRunning` reformulation is not refuted (it concerns a slab of fixed physical size, and these slabs are on
  the magnetic side), but it shows that a running set defined by the action density alone is too wide here: the
  remnant `epsilon` for such a set would be about 0.6, far above 1/20.
- Frozen faces are still the extreme (`-5.1` at `T = 2`), but the worst typical pair (`-3.7`) is not far behind. The
  factor depends on more of the face than its action density; a running set that works needs a finer criterion (for
  example the faces' Polyakov-line content along the twist direction), which is a question for the next round [reading].

**Not run:** larger cross-sections; a correlation study of `log c` against face observables (the data to do it are not
saved per pair).
