# The encoder at a boundary, tested on three use cases

Status: 2026-11-23. Lean: `ProofPhase/Unified/Encoder.lean` (general), `ProofPhase/Unified/EncoderInstances.lean` (three
use cases); `encoder-axioms.sh` and `encoder-axioms.log` (56 declarations, standard axioms only, no sorry). Third-layer
check: `encoder_check.py` and `encoder_check.log` (CPU, seconds). Builds on the ledger of `UNIFIED.md`. The owner's readings
this answers are recorded in `docs/mass-gap/weak-coupling/PREP.md`, from the entry "GRH reads the ledger in two separate
ways" to the end.

Status marks: **Lean** (proved in this repository), **classical** (standard theorem, not in Lean here), **numerical**
(checked by `encoder_check.py`), **external** (proved elsewhere, recorded but not checked here), **reading** (an
identification with DMP vocabulary, not a theorem), **open** (not proved), **fails** (the requirement does not hold in
this form).

## 1. In plain words

A boundary has two sides. The encoder is what the boundary passes on: one state, seen once from the inside and once,
after one rotation, from the outside. Both sides certify the same size for it. That shared size is the shared root. The
encoder carries exactly one number: how much the state overlaps with its rotated image. This is the **reflection
coefficient** `c`.

Positivity (the space has an honest, never-negative norm) forces `|c| <= 1`. The step's factor in the ledger is then a fixed
function of `c` and nothing else:
- `c = 0` (no reflection) gives factor exactly 1 and cost 0, a lossless step. Zero and one are one certificate.
- `|c|` strictly below 1 gives a factor finitely below 1.
- `|c| = 1` is the closure, where the factor reaches 0.

Reading `c` from the other side conjugates it, and the factor stays the same. A symmetry of the space moves the encoder
without changing `c`. The inside meets the outside only through the boundary label (the Markov property). What a step
leaves behind is the remainder after the rotated image is removed. A chain of such remainders is the bulk tail.

All three use cases fit this shape. Their verdicts differ:
- **Yang-Mills** fits every requirement in Lean except the last. The open step O1 becomes one inequality on the encoder:
  the twist ratio `Z_tw/Z` must stay above `(mu - 1)/(mu + 1)`, about 0.74, for every outside. The hand-over point sits at
  the encoder's self-dual value `sqrt 2 - 1`, about 0.41, which is not enough.
- **GRH** fits, with the encoder exactly the Szego step (numerical to 5e-13, classical). But the shared root and the Markov
  step hold in every finite model, whether or not the zeros are on the line. The only requirement that tells the cases
  apart is `|c| <= 1` itself, and that is GRH.
- **NP vs coNP** fits in the label, in Lean, but the factor comes out exactly 1. The crossing label is passed on without
  loss, and a cutting-planes line names it at factor 1. So the encoder can explain resolution's cost (a clause of width `w`
  keeps at most `1 - w/2n`) but cannot supply the crossing cost for strong systems.

## 2. The definition

**Encoder** (`Encoder`, Lean). Data:
- a space of boundary states with a positive form (an inner product over the reals or the complex numbers);
- a state `psi` (passed on by the inside) and a state `psi'` (the same boundary seen from the outside, `psi' = R psi` for
  the one rotation `R`, linear or antilinear, `Encoder.ofRot`);
- the shared root `||psi'|| = ||psi|| > 0`.

Nothing else. The encoder's number is the reflection coefficient

    c = <psi, psi'> / ||psi||^2.

**The factor is determined by `c` alone.** Two loss profiles occur, and both are norm shares of a projection fixed by the
rotation:

| profile | factor | meaning (Lean) | where |
|---|---|---|---|
| Szego | `szego c = 1 - abs(c)^2` | the share of `psi` left after removing its projection on the mirror image: `abs(psi - conj(c) psi')^2 = abs(psi)^2 (1 - abs(c)^2)` (`szego_remainder`) | GRH |
| electric | `elec c = (1 - c)/(1 + c)` | the odd part over the even part under the rotation: `abs(psi - psi')^2 / abs(psi + psi')^2 = elec(re c)` (`encoder_elec`) | Yang-Mills |

The cost in the ledger is `-log(factor)`, and a chain of encoder factors is a ledger with floor 0 (`pays_of_factors`, Lean).

**What the readings require, and where each sits in the definition** (all Lean, general):

| requirement | in the encoder | Lean |
|---|---|---|
| factor in (0, 1]: exactly 1 or finitely below | positivity gives `abs(c) <= 1`, so the Szego factor is in `[0, 1]`; it is 1 exactly at `c = 0` and positive exactly for `abs(c) < 1`; the electric factor is in `(0, 1)` for `0 < c < 1` and is 1 at `c = 0` | `norm_refl_le`, `szego_mem`, `szego_eq_one_iff`, `szego_pos_iff`, `szego_eq_zero_iff`, `elec_mem`, `elec_eq_one_iff` |
| zero and one are one certificate | cost 0 exactly when factor 1; cost at least 0 exactly when factor at most 1 | `cost_eq_zero_iff`, `cost_nonneg_iff` |
| one rotation acts on the encoder | `psi' = R psi`; a symmetry `S` of the form moves the encoder without changing `c` | `Encoder.ofRot`, `Encoder.refl_map` |
| shared root | `abs(psi') = abs(psi)`; read from the other side, `c` is conjugated and both profiles give the same factor | `Encoder.root`, `refl_swap`, `szego_swap`, `elec_swap` |
| Markov property | a joint weight that factorises through the label: the inside's law given the label does not depend on the outside, and each label's weight is (inside part) x (outside message) | `markov_conditional`, `markov_sector` |
| bulk tail as the only remainder | the step leaves the remainder after the rotated image (`szego_remainder`); a chain of steps leaves the product of the factors, and a uniform bound of the factors below `e^{-delta}` is exactly a cost above the floor `delta`, hence a summable tail | `costAboveFloor_of_factor_le`, `factor_le_of_costAboveFloor`, with `rate_of_costAboveFloor` (`Ledger.lean`) |

**The electric profile's own duality.** `elec` is an involution, `elec(elec c) = c` (`elec_elec`, Lean): electric and
magnetic exchange roles. Its self-dual point is `c = sqrt 2 - 1` (`elec_selfdual`, Lean), with cost
`-log(sqrt 2 - 1) = log(1 + sqrt 2) = 0.8814` (`selfdual_cost`, Lean). That is the project's hand-over value: the 0.881
hand-over is the fixed point of the encoder's duality. It is also the classical Kramers-Wannier self-dual coupling of the
2D Ising model [classical].

**The hand-over in encoder terms.** A uniform distance of every factor below `e^{-delta}` is the cost above the floor
(Lean, both directions). For the electric profile with floor `log mu`, `oneBox_iff_refl` (Lean) gives:

    cost above log mu for every outside  <=>  c >= c0 > (mu - 1)/(mu + 1) for every outside.

## 3. The three use cases

### 3.1 Yang-Mills: the centre twist on the box boundary

**The encoder.** The label on the box boundary is a plane plus a centre element. The one rotation is the centre twist
`U` (in SU(2), the element -1, a rotation by 2 pi). The encoder's state is the box's thermal state, so `<psi, psi> = Z`
and `<psi, U psi> = Z_tw` (the trace with the twist operator inserted) [classical; transfer-matrix form of 't Hooft's
twist]. So `c = Z_tw/Z`. The electric profile gives the electric flux ratio `Z_{e=1}/Z_{e=0}`. The toy check confirms
`Z_{e=1}/Z_{e=0} = elec(Z_tw/Z)` and `abs(psi - U psi)^2 / abs(psi + U psi)^2 = elec(c)` to 12 digits [numerical].

| requirement | status | content |
|---|---|---|
| factor determined by the encoder | **Lean** | `ym_factor`: `elec(Z_tw/Z) = e^{-F_e}` (from `one_sub_two_flipP_exp`, `elecF`) |
| factor in (0, 1] | **Lean** | `su2_encoder`: for SU(2), every `beta != 0`, every `L`, every even `T`, the factor is in `(0, 1)` (`su2_Ztw_lt_Z`; `0 < Z_tw` stated as a hypothesis, as in `su2_handover`). It is exactly 1 only in the limit `Z_tw/Z -> 0`, the weak-coupling end [classical, semiclassical] |
| one rotation on the encoder | **Lean** | `ym_encoder_rotation`: the lattice rotation (0 2)(1 3) moves the twist from plane 01 (electric) to plane 23 (magnetic) with the same factor (`tHooft_rotation`, `electric_eq_magnetic`). That the lattice quarter-turn and the internal centre element -1 are "the same rotation" is [reading]; both are the nontrivial centre of an SU(2), with Spin(4) = SU(2) x SU(2) [classical] |
| shared root | **Lean** | `exists_sheet_both_sides`: for a closed centre layer the flux label is carried by a sheet face on both sides of every flux cell, so both sides see the same label; both sides read the same factor (`elec_swap`) |
| Markov property | **classical**, general form **Lean** | a nearest-neighbour Gibbs measure is Markov across a boundary [classical]; the factorisation lemma is general Lean (`markov_conditional`, `markov_sector`) and is not instantiated for the Wilson measure here |
| bulk tail as the only remainder | **open** (O1) | `ymOneBox_iff_refl` (Lean): `YMOneBox` holds exactly when `Z_tw/Z >= c0 > (mu - 1)/(mu + 1)` for every outside. With `mu_4 = 6.77` that is `Z_tw/Z > 0.743` (factor below `1/mu = 0.148`) [numerical]. The hand-over encoder is self-dual at `c = sqrt 2 - 1 = 0.414` and lies below the bound for every `mu >= 3` (`handover_refl`, Lean) |

**Verdict: fits.** Five of six requirements are Lean or classical. The sixth is O1, now stated as one inequality on the
encoder.

### 3.2 GRH: the Szego scale step

**The encoder.** At scale step `m`, `u = z phi_{m-1}` (the previous monic orthogonal polynomial, shifted by one). The one
rotation is the Szego mirror: reversal of the coefficients at degree `m` with complex conjugation, `u -> u*`. It is
antilinear. The form is the Toeplitz form. The reflection coefficient of the encoder `(u, u*)` is the Szego (Verblunsky)
coefficient `k_m` [classical: Szego recursion]. `encoder_check.py` confirms `abs(c)^2 = abs(k_m)^2` at every step in both
finite models, to 5e-13 [numerical]. The factor is the Szego profile `1 - abs(k_m)^2`, the ratio of consecutive margins
[classical: Levinson-Durbin]. Offset from the line is the exponent, and the modulus of the atom is the factor. The closure
`abs(k_N) = 1` marks a finite existence space exhausted.

| requirement | status | content |
|---|---|---|
| factor determined by the encoder | **classical**, **numerical**; **Lean** for the lag encoders | the step's factor is `1 - abs(k_m)^2`, the encoder's Szego factor (`szego_remainder` gives its meaning in general). `grh_lag_encoder` (Lean): under the sign, the lag encoder (`z^m` against its image `1`) has `c = t(m)/t(0)` in the closed unit disk and Szego factor in `[0, 1]`; for `m = 1` this is the first Szego step |
| factor in (0, 1] | **open** (the sign) | `abs(k_m) <= 1` at every step is `ScaleSign`, equivalently positivity of every section (`scaleSign_iff`, Lean). In the finite model: on the line every step is inside the disk and the closure is `abs(k_10) = 1.000000000`; one pair off the line by 0.05 gives `abs(k_9) = 1.124` and `abs(k_11) = 1.919`, negative factors [numerical]. One encoder outside the disk refutes the sign (`sign_fails_of_refl`, Lean). Over the integers there is no closure, and the requirement is `abs(k_m) < 1` strictly (`grh_margin`, Lean) |
| one rotation on the encoder | **classical**, **numerical** | the Szego mirror `u -> u*`; on the atoms it is the functional-equation pairing `z <-> 1/conj(z)`, which fixes an atom exactly when it lies on the circle (`atoms_on_circle`, Lean). That it is the same rotation as Yang-Mills' centre twist is [reading] |
| shared root | **classical**, **numerical** | `<u*, u*> = <u, u>` for every Hermitian Toeplitz form (persymmetry) [classical]; checked to 2e-13 in both models, on and off the line [numerical]. **It holds whether or not GRH holds.** |
| Markov property | **classical**, **numerical** | each scale step uses only `k_m` and the previous margin (the recursion is first order in scale) [classical] |
| bulk tail as the only remainder | **external** for zeta and Dirichlet, **open** beyond | RH is equivalent to every remnant `x^rho` having the same tail `x^{1/2}`: `psi(x) = x + O(x^{1/2} log^2 x)` (von Koch 1901) [classical]. PREP records this as established for zeta and Dirichlet L-functions by others' Lean proofs, by a route that does not use positivity [external, not checked here]. Open beyond Dirichlet |

**Verdict: fits, but the open step is the bound itself.** In Yang-Mills and NP vs coNP, "factor at most one" is proved and
what is open is a uniform distance below one. In GRH, "factor at least zero", that is `abs(c) <= 1`, is itself the open
step. The encoder's other requirements (shared root, Markov, rotation) hold in every model and do not separate the
on-line case from the off-line one. Off the line the form is indefinite: smallest eigenvalue `-2.1e-4` [numerical]; Krein
form, `krein_off_line` (Lean).

### 3.3 NP vs coNP: what a proof line names about a crossing

**The encoder.** The boundary of a vertex set `S` in a Tseitin system. Its label is the parity of the true boundary edges,
and the parity summary is one line that names it. The one rotation is the flip of a boundary edge, which toggles the
parity. A restriction (fixing one variable to one value) is a step. The step's factor for a line is the share of
restrictions that leave the line alive (`survShare`, Lean).

| requirement | status | content |
|---|---|---|
| factor determined by the encoder | **Lean** | `survShare` depends only on which assignments the line names. A clause naming `w` literals keeps at most `1 - w/(2n)` (`clause_share_le`, Lean; exactly `1 - w/(2n)` for `n = 6`, numerical); the threshold line `thr B k`, `k >= 2`, keeps 1 (`thr_share_one`, Lean, from `thr_survives`); so does the parity line [numerical] |
| factor in (0, 1] | **Lean** | `survShare_mem`: always in `[0, 1]`. Resolution: finitely below one. Cutting planes: exactly one |
| one rotation on the encoder | **Lean** | `toggle`: flipping a boundary edge toggles the parity at its vertex. For a boundary law of fixed parity the flip gives `c = 0`: the label is passed on losslessly, with both factors equal to 1 [numerical] |
| shared root | **Lean** | `flux_fixed`, `summary`: the inside fixes the boundary parity to its charge, whatever the interior does. `split_unsat_iff`: a split formula `A(x, y) and B(x, z)` is unsatisfiable exactly when the two boundary laws share no value. **A refutation is the certificate that the two sides share no root** |
| Markov property | **Lean** | `split_unsat_iff`: the two sides interact only through the shared variables `x`; `invisible`: an edge not at `v` does not affect `v`'s constraint |
| bulk tail as the only remainder | **open** (`CrossingCost`) | the costly lines left after `b` steps. For resolution the tail exists (Ben-Sasson and Wigderson, `resolution_meets_form`, Lean); for strong systems it is open |

**Verdict: fits in the label, fails to give a cost.** The encoder (the crossing label) is lossless: its factor is exactly 1,
and a cutting-planes line names the whole crossing at factor 1 (`thr_share_one`, `majority_line`, Lean). So for strong
systems the crossing cost cannot come from the encoder. Resolution pays because a clause names its label through
literals, and any one literal kills it.

## 4. The fit table

| requirement | Yang-Mills | GRH | NP vs coNP |
|---|---|---|---|
| factor determined by the encoder alone | Lean (`ym_factor`) | classical + numerical (`k_m` = overlap with mirror); Lean for lag encoders | Lean (`survShare`, `clause_share_le`, `thr_share_one`) |
| factor in (0, 1], exactly 1 or finitely below | Lean (`su2_encoder`; `0 < Z_tw` stated) | **open** (the sign); numerical: holds on the line, fails off it | Lean (`survShare_mem`); exactly 1 for cutting planes |
| one rotation acting on the encoder | Lean (`ym_encoder_rotation`); "same rotation" reading | classical + numerical (Szego mirror); "same rotation" reading | Lean (`toggle`); numerical (`c = 0`) |
| shared root | Lean (`exists_sheet_both_sides`, `elec_swap`) | classical + numerical; holds in every model | Lean (`flux_fixed`, `split_unsat_iff`): a refutation certifies there is none |
| Markov property | classical; general Lean | classical + numerical | Lean (`split_unsat_iff`, `invisible`) |
| bulk tail as the only remainder | **open** (O1 = `Z_tw/Z > (mu-1)/(mu+1)`, Lean equivalence) | external (zeta, Dirichlet); open beyond | **open** (`CrossingCost`); resolution Lean |
| verdict | **fits**; open step is one inequality on `c` | **fits**; open step is `abs(c) <= 1` itself | **fits in the label; fails to produce a cost** for strong systems |

## 5. What does not fit

1. **Two loss profiles, not one.** The factor is always a function of `c` alone, but the function differs between Yang-Mills
   (`(1 - c)/(1 + c)`) and GRH (`1 - abs(c)^2`). Both are norm shares of a projection fixed by the rotation, both give 1 at
   `c = 0` and 0 at the closure, and both read the same from either side (Lean). The electric profile also needs the
   rotation to be an involution and `c >= 0` (positivity of the twisted weight, `0 < Z_tw`, stated, not proved here).
2. **The Yang-Mills encoder state is a trace.** `Z = <psi, psi>` and `Z_tw = <psi, U psi>` hold for the thermal (purified)
   state [classical]. The Lean instance works with the numbers `Z` and `Z_tw` from the lattice integrals, not with a
   Hilbert-space encoder.
3. **GRH in Lean covers only the lag encoders.** `t(m)/t(0)` is an encoder of the Toeplitz form, and `m = 1` is the first
   Szego step. That `k_m` for `m >= 2` is the overlap of `z phi_{m-1}` with its mirror image is classical and numerical,
   not Lean.
4. **GRH's shared root and Markov step do not discriminate.** They hold in every finite model, off the line included.
   Positivity alone separates the cases.
5. **NP's encoder is lossless.** The crossing label passes with factor exactly 1, so the encoder determines resolution's
   cost but not the crossing cost of a strong system. The NP column of the table holds; it is the conclusion that fails.
6. **The Markov property for the Wilson measure** is classical and is not instantiated in Lean. Only the general
   factorisation lemma is in Lean.
7. **The finite closure gives factor 0**, not a factor in (0, 1]. In the finite GRH model the closure `abs(k_N) = 1` is
   reached exactly. Over the integers there is no closure, and the requirement is `abs(k_m) < 1` strictly.

## 6. What the encoder says each open step needs

- **O1 (Yang-Mills).** A uniform lower bound on one number: at the hand-over box, for every outside,
  `Z_tw/Z >= c0 > (mu - 1)/(mu + 1)` (0.743 for `mu_4 = 6.77`). This is exactly `YMOneBox` (`ymOneBox_iff_refl`, Lean).
  In words, the twist must be nearly free at that box, 't Hooft's magnetic-disorder criterion for confinement [classical].
  The proved hand-over reaches the self-dual point `c = sqrt 2 - 1 = 0.414` (`handover_refl`, Lean). The gap between 0.414
  and 0.743 is what O1 has to close. Nothing else in the encoder is missing; the Markov step for the Wilson measure is
  classical.
- **The sign (GRH).** Every scale encoder in the closed unit disk, `abs(k_m) <= 1`, from the primes, the characters and the
  real place alone. The encoder adds no handle beyond this. Its rotation, shared root and Markov step come free in every
  model, so the whole content is positivity of the one form (the irreducibility of G0, `GRH/Transfer.lean`). An encoder
  outside the disk would refute it (`sign_fails_of_refl`, Lean).
- **The crossing cost (NP vs coNP).** Not from this encoder. The label is passed on losslessly (`c = 0`), and a
  cutting-planes line names it at factor 1 (`thr_share_one`, Lean). A cost has to come from a step that is not a
  restriction. The Lean candidate is the rounding step: every cutting-planes refutation needs a rounding of a combination
  of at least two lines (`refutation_needs_pair`, `CPPairs.lean`). Whether that step has a factor finitely below one is
  open. In encoder terms, the step has to read two boundaries at once, not one.

## 7. DMP mapping (all [reading])

- The DB is the boundary where the encoder lives. An act happens only there, and only the encoder matters there [reading].
- The reflection coefficient `c` is the influence of the possibility space at that boundary. `abs(c) <= 1` is causality at
  that scale, and `abs(c) = 1` is the closure of a finite existence space [reading].
- The shared root is "certified to be tied to the same root as another node", the owner's definition of entanglement: both
  sides certify the same norm [reading].
- The one rotation: the centre element -1 of an SU(2) (2 pi), the Szego mirror, the parity flip [reading].
- Zero and one as one certificate: `c = 0`, cost 0 and factor 1 are one statement (Lean). Calling it the vacuum or the line
  is [reading].
- The hand-over as the self-dual point of the encoder's duality (Lean for the number `log(1 + sqrt 2)`). Calling it the
  point where finite goes to infinite is [reading].
- The bulk carries only the tail of its remnants: the product of the remainders (Lean form). The YM instance is O1, the
  GRH instance von Koch's tail [reading for the identification].

## 8. Files

- `docs/mass-gap/formal/ProofPhase/Unified/Encoder.lean`: the definition and the general theorems.
- `docs/mass-gap/formal/ProofPhase/Unified/EncoderInstances.lean`: the three use cases (build target).
- `docs/unified/encoder-axioms.sh`, `encoder-axioms.log`: build and `#print axioms` for all 56 declarations.
- `docs/unified/encoder_check.py`, `encoder_check.log`: the CPU check (GRH overlap identity, Yang-Mills duality, NP shares).
