# Does GRH imply O1? The precise statement and where it breaks

Status: 2026-11-24. Decision round on the question "is O1 (the Yang-Mills open step) conditional on GRH?". **It came out
negative: no implication, with the break named exactly.** GRH, O1 and the mass gap stay open; nothing here proves any of
them.

Lean: `docs/mass-gap/formal/ProofPhase/Unified/GRHToO1.lean` (new). Axioms: `grh-to-o1-axioms.sh`,
`grh-to-o1-axioms.log` (46 declarations: 45 on the standard axioms, 1 on none; no `sorry`, `admit`, `axiom`,
`native_decide`).

**Status marks.** **[Lean]** proved in Lean here or earlier in the repository, standard axioms only; **[classical]**
known mathematics, recalled; **[external]** proved by others, cited (an audit item where the paper uses it);
**[reading]** an identification with DMP vocabulary, not a theorem; **[open]** not proved by anyone.

---

## 0. In plain words

**The answer.** GRH does not imply O1 by any route known here or in the literature, and in the form the paper states
both (two problem cards of one API) the implication is provably empty. Lean shows three things. First, O1 is the same
thing as a *uniform ratio bound* on the two electric sectors of the hand-over box, and the same thing as a positivity
*with a strict margin* of the sector form shifted by the path entropy. So the "uniform ratio bound" that earlier rounds
named as the missing bridge is not a smaller statement than O1: it is O1. Second, GRH, in every form the project uses
(Mathlib's Riemann hypothesis, Dirichlet GRH, Weil positivity at every scale), is a statement about zeta data only. The
Yang-Mills card takes the gauge data as free input, and some input breaks O1. Logically, "GRH implies O1 for every input"
is then *equivalent to "GRH is false"*. Any real proof would need an extra statement that ties the sector weights of the
hand-over box to the zeros. No such statement is known, and it would be at least as hard as O1 itself (`ZetaCoupling`).

**Why the owner's lead does not close the gap, and what it does show.** The lead was: GRH is tuned towards O1 by
positivity, from the median (the critical line), and its irreducibility gives the floor. Lean makes the meeting point
exact. The positivity GRH supplies is a sign **with zero margin**: in the project's own finite model with `k` zeros on
the line, the Toeplitz form at scale `k` is nonnegative and has a null vector, so no positive margin is certified
(`grh_margin_exactly_zero`). O1 needs a margin strictly above zero, uniform over outsides, and for a different form
(the sector form shifted by `mu`, at the hand-over, not at the median). A sign cannot be turned into a margin by
positivity alone: positive sector weights with O1 false exist (`positivity_without_o1`). The one model where zeta
literally is a Yang-Mills partition function confirms this from the other side. In two-dimensional SU(2) on a closed
surface, `Z = zeta(2g - 2)`, and the two electric sectors are `2^-s zeta(s)` and `(1 - 2^-s) zeta(s)`. Zeta cancels from
every sector ratio. The O1-type statement there is decided by one Euler factor (the prime 2), and the zeros never enter.
The later leads (a certified margin at the start `{infinity, 2, 3}`, its multiplicative transport, the tick as
Birkhoff-Hopf) share one geometry with O1 but ask the opposite of it. Transporting Weil's margin needs ticks that lose
little; O1 needs boxes that lose at least the path entropy. Neither implies the other (section 3a). So: the floor the owner describes (a gap that makes each tick binary, never below the error bars) is exactly what O1
would give. GRH's irreducibility supplies the sign, not the floor.

---

## 1. The precise statement

**Which GRH.** Three forms are in the project; each is tested.

| name | statement | Lean | status |
|---|---|---|---|
| RH | Mathlib's `RiemannHypothesis`: nontrivial zeros of zeta have real part 1/2 | `ExtRH` (`GRH/TieIn.lean`) | [external] slot, open |
| Dirichlet GRH | every zero of `L(chi, s)` in `0 < Re s < 1` has real part 1/2 | `ExtDirichletGRH` | [external] slot, open |
| Weil positivity (the card's open step) | `ScaleSign t`: the Toeplitz form of the moments is positive at every scale | `API/GRH.lean`, `Unified/GRH.lean` | open beyond the finite model; RH implies it for zeta models (`tie_in`) [Lean] |

**Which O1.** The open step of the Yang-Mills card (`API/YangMills.lean`):
- `YMOneBox Fe mu`: there is `kappa > log mu` with `Fe(omega) >= kappa` for every outside `omega` [open];
- `Fe` is the electric free energy of the hand-over box (fixed physical size `L_h`), `mu = mu_4 = 6.77` the path entropy
  per box [classical], the for-all runs over every well-defined outside (boundary condition) of that one box;
- with sector weights `p0 = Z_{e=0}`, `p1 = Z_{e=1}` (both positive per finite lattice [Lean]), `Fe = log(p0/p1)`
  (`cost_eq_log_ratio`, from `z2_sectors`) [Lean].

**O1 in the two forms the bridge question needs** [Lean]:
- `ymOneBox_iff_ratio`: O1 holds exactly when some `mu' > mu` has `mu' p1(omega) <= p0(omega)` for every outside. This
  is the uniform ratio bound of `GRH-LENS.md` 6.5. It is O1 itself.
- `ymOneBox_iff_margin`: O1 holds exactly when the shifted sector form `p0 - mu p1` is at least `delta p1` for one
  `delta > 0`, uniformly. O1 is a positivity with a strict, uniform margin.

**What "GRH implies O1" would have to mean.** A proof of `G -> YMOneBox Fe mu_4` for the actual SU(N) Wilson weights of
the hand-over box, with `G` one of the three forms above, and with the hypothesis `G` used. Classically,
`G -> O1` is the same as `not G or O1` [classical logic]; a proof that does not use `G` is a proof of O1.

## 2. No implication through the cards

**The Lean** (section 2 of the file):
- `badInput`, `badInput_not_open`: a Yang-Mills input (one outside, two continuations, electric cost 0) on which O1
  fails [Lean].
- `imp_all_iff_not`: for any statement `H` and any card whose open step fails on some input,
  `(H -> every input satisfies the open step) <-> not H` [Lean].
- `rh_imp_card_iff`, `dirichlet_imp_card_iff`, `grhCard_imp_card_iff`: the three GRH forms in that place [Lean]. So
  "RH implies O1 on every input of the card" *is* "RH is false". A proof of the first would disprove RH.
- `pair_model`: a GRH input (one zero at the centre, weight 1) whose open step and conclusion hold, next to a Yang-Mills
  input whose open step fails [Lean].

**What it means.** The cards are honest: each takes its content as input. GRH speaks about zeta; O1 speaks about gauge
weights. A bridge has to be input-specific: it must use a statement that mentions the hand-over box's weights and
zeta's zeros together. Call that a coupling. Section 5 names it in Lean.

## 3. The owner's lead: positivity from the median

The lead (`PREP.md`, last entry): GRH is attuned by positivity towards O1, from the median. Its exact counterpart, recorded
there: the median is the critical line, Weil's criterion is a positivity about it, Yang-Mills has reflection positivity,
and the bridge needs positivity with a margin. This round makes the comparison of margins exact.

**GRH's positivity has margin exactly zero** [Lean]:
- `exists_null`: for `k` atoms, the coefficients of `prod (X - z_i)` form a vector on the cells `0 .. k` with last entry
  1 whose polynomial vanishes at every atom.
- `toepForm_atoms_null`: the Toeplitz form of the atoms' moments vanishes on that vector (any weights, any nonzero atoms).
- `no_margin_at_closure`: hence no positive margin is certified at scale `k`.
- `grh_margin_exactly_zero`: in a `ZeroModel` with multiplicity weights, under the card's open step `ScaleSign` (GRH in
  the finite model), the section at scale `k` is positive with margin 0, and every certified margin is `<= 0`.

This is the Lean form of "margin exactly 0 at a finite closure" (`ENCODER.md` 3.2, `GRH-LENS.md` 6.5). It matches the
transport theorem's "zero slack" fact (`TRANSPORT.md` 1): uncertainty and margin carried by one factor leave no
damping.

**O1 needs a strict margin** (`ymOneBox_iff_margin`) [Lean], for a different form: the sector form shifted by the path
entropy `mu`, at the hand-over box, uniformly over outsides.

**Positivity does not choose the side** [Lean]: `positivity_without_o1` gives positive weights in both sectors (the
encoder strictly inside the disk) with O1 false, for every `mu >= 1`. This is Verblunsky freeness in its simplest case
(`z2_realize`, `GRH-LENS.md` 3).

**Verdict on the lead** [reading on top of Lean]. The route "from the median, through positivity" is real as a shared
shape: Weil positivity and reflection positivity are both positivity about a mirror [classical]; Connes reads Weil
positivity as a trace-formula positivity [external, pointer]. But the shared positivity is a sign, and the sign is
already proved on the Yang-Mills side (`Z_e >= 0`, `0 < c < 1` per finite lattice) [Lean]. What O1 asks beyond it is a
margin. GRH has no margin to hand over; it has zero margin, provably, at every finite closure.

**The owner's floor reading** (`PREP.md`: the gap makes each tick binary; the floor is always at least the existence tied
to the error bars). Exact counterpart: a floor at a finite resolution gives settling at that resolution
(`reaches_of_contracting`) [Lean, with the floor as hypothesis]; keeping the floor positive as the resolution goes to zero
is O1 [open]. GRH contributes no floor: in the finite model its form is degenerate exactly at the closure, the opposite
of a floor. So the floor reading describes what O1 would deliver, not something GRH supplies [reading].

## 3a. The margin at the start, its transport, and the tick (three later leads)

The leads (`PREP.md`, last entries):
1. **The margin exists at the start.** At the universal start `{infinity, 2, 3}`, Weil's form on supports up to
   `a = 0.69` is positive with a certified margin (`GRH-ONEBOX-CERT.md`: `c = 1.5e-9`, `3.4e-11`, `6.4e-13` at
   `a = 0.60, 0.65, 0.69`) [numerical, certified in ball arithmetic; Lean for the abstract step, `GRH/OneBoxCert.lean`].
2. **Carrying it outward** needs a step multiplicative in the margin (`INDUCTION.md` 1).
3. **That step is the tick operator**, an act at a DB rotating, read as Birkhoff-Hopf: a positive map whose image cone
   has finite Hilbert projective diameter `Delta` contracts by `tanh(Delta/4)`.

The question: is this one statement shared by GRH and O1?

**Answer: no.** The shared *object* is real: one per-tick hyperbolic distance `d` of an encoder from the lossless point.
The Szego factor is `1 - |c|^2 = 1/cosh^2(d/2)` and the electric factor `e^{-d}` (`szego_of_elec`, `elec_cost`) [Lean].
But the two problems ask for **opposite one-sided bounds** on it, on different encoders.

| statement | in the tick's distance `d` | on which encoder | status |
|---|---|---|---|
| GRH (the sign) | `d_N < infinity` at every tick (`abs(k_N) < 1`) | Verblunsky `k_N` of the zero measure, one per grid step | [open] |
| GRH, multiplicative transport (`lambda(a + delta) >= (1 - kappa delta) lambda(a)`) | `d_N <= D` uniformly: an **upper** bound on the distance, a **lower** bound on the factor | same | [open]; sufficient for the sign, not needed by it |
| GRH, uniform margin (`inf_a lambda(a) > 0`) | `sum_N tanh^2(d_N/2) < infinity` (the Szego condition) | same | **false** for zeta's zero measure [classical]; exactly 0 at the closure of a finite model [Lean] |
| O1 | `d >= kappa > log mu` for every outside: a **lower** bound on the distance, an **upper** bound on the factor | the twist ratio `Z_tw/Z` of the hand-over box, one per outside | [open] |
| Birkhoff, uniform `Delta` (two-sector cone) | the spread `abs(d(omega) - d(omega'))` over outsides is bounded | same as O1 | [open]; independent of O1 [Lean] |

**The Lean** (section 6 of the file):
- `o1_ticks_kill_margin`, `uniform_margin_excludes_o1`: take one sequence of ticks whose encoders stay at least
  `theta > 0` from the lossless point (O1 at each tick). Then the Szego product `prod (1 - c_n^2)`, the carried margin,
  falls below every `m > 0`. A uniform margin and O1 at every tick exclude each other [Lean].
- `transport_not_decay`, `decay_not_transport`: the multiplicative transport and O1 in factor form are independent
  [Lean].
  - `TransportStep`: one positive lower bound on every factor. `DecayStep`: one upper bound `rho < 1/mu`.
  - Lossless ticks transport and fail O1. Factors `2^{-n}/(2 mu)` satisfy O1 and transport nothing.
  - Both together make a two-sided band. Nothing ties the band of one encoder sequence to the other's.
- `spread_without_o1`, `o1_without_spread`: on the two-sector cone, bounded Birkhoff spread and O1 are independent
  [Lean].
  - Bounded spread with O1 false: all outsides at ratio 1, spread 0.
  - O1 with unbounded spread: ratios `e^{-n}/(2 mu)`.
  - So "the tick's image has uniformly bounded projective diameter" is not O1's uniform ratio bound. O1 is a *location*
    of the image (on the far side of the ray at ratio `1/mu`), not its *size*.
- `sec_restrict`: a margin at scale `k + 1` is one at scale `k` [Lean]. Growing support restricts one form to nested
  sections.

**Does the GRH side factor into ticks of a positive map?** It breaks in three places:
1. **Growing support is restriction, not iteration** (`sec_restrict`) [Lean]. The margin is non-increasing because the
   test spaces are nested (`INDUCTION.md` 1, "monotone margin"). No map carries `W_a` to `W_{a'}`.
2. **The Szego recursion does factor the margin into ticks, but they are isometries.**
   - `E_N = E_{N-1}(1 - k_N^2)` [classical].
   - The step from `N - 1` to `N` is a transfer matrix in `SU(1,1)` up to the factor `z`, with a new `k_N` at each
     step.
   - As a map of the two-dimensional cone `{abs(b) <= abs(a)}` it is an automorphism. Its image is the whole cone, so
     `Delta = infinity`, and Birkhoff-Hopf gives the factor `tanh(infinity) = 1`: no contraction [classical].
   - This matches `GRH-LENS.md` 6.5: all GRH operations are isometries or signs.
   - **At the start `{infinity, 2, 3}` too.** The start's margin `c(0.69) > 0` is room in a *form*, not a finite
     diameter of a *map*. The step has `Delta = infinity` there as everywhere.
3. **Primes enter additively, and with indefinite forms.** In the explicit formula each prime power `n` adds
   `-Lambda(n) n^{-1/2} [h(log n) + h(-log n)]` (`INDUCTION.md` 1). As a quadratic form in `f` this is a symmetrised
   translation by `log n`, which is indefinite [classical]. Adding it consumes margin; it is not a positive map composed
   with the previous one. Two-term bounds only add (`two_term_bound`, `GRH/Transfer.lean`) [Lean].

**What uniformity in the tick would give and need on each side.**
- **GRH.**
  - A uniform lower bound on the tick factors (`d_N <= D`) would carry the start's positive margin to every support.
    The margin would stay positive, decaying at most exponentially, so this would prove the sign [reading on top of
    `Transfer.lean`'s `margin_pos_of_factors`].
  - It needs control of every `k_N` of the zero measure, which is the open step itself in quantitative form.
  - The numbers point against a uniform `D`: the drop per 0.01 of support grows (0.32, 0.40, 0.41;
    `GRH-ONEBOX-CERT.md` 5) [numerical].
  - A *uniform margin* (`inf lambda > 0`) is false. The zero side of the explicit formula is purely atomic, so by
    Szego-Kolmogorov-Krein the product of the factors is `exp(integral log w_ac) = 0` [classical]. Concretely,
    functions of support `2a` concentrate in the zero-free gap `abs(gamma) < 14.13` (`INDUCTION.md` 1, Slepian).
- **O1.**
  - A uniform upper bound on the box factor below `1/mu` (`d >= kappa > log mu`) for every outside *is* O1
    (`ymOneBox_iff_ratio`) [Lean].
  - Birkhoff-Hopf with a uniform `Delta` for the full transfer kernel would give a spectral gap per tick directly
    [classical]. That is a different, stronger named statement (condition A of `GRH-LENS.md` 6.5). It is also open, and
    bounded spread on the two-sector cone does not imply it.
- **Shared?**
  - The ledger is shared: `Pays`, `carry` and `Ledger.contract` are one theorem for both [Lean]. What each problem asks
    of the tick factor is not.
  - GRH (sign and transport) asks that ticks lose *little*: factor bounded away from 0. O1 asks that boxes lose *a
    lot*: factor below `1/mu`.
  - This is `GRH/Transfer.lean` item 1 made exact: contraction is the wanted decay in Yang-Mills and the harmless
    collapse of the margin in GRH.
  - The two points of view are one rotation apart: the half-turn swaps the Szego and electric pictures
    (`GRH-LENS.md` 6.2) [Lean]. But a symmetry exchanges pictures. It does not turn an upper bound on one encoder into a
    lower bound on another (`GRH-LENS.md` 6.3).

**Named exactly.** The bridge the leads point to would be one tick sequence whose factors lie in a band
`e^{-D} <= f <= e^{-kappa}`, `kappa > log mu`, uniformly. Its lower edge would transport Weil's margin and its upper edge
would bound the hand-over box. No known object has both the zero measure's Verblunsky steps and the box's sector ratios
as its ticks, and no known result supplies either edge. So it is not one statement shared by both problems: it is two
open statements in one geometry.

## 4. The one model where zeta is the partition function

**The model** [external: Witten 1991, CMP 141; classical for the representation theory]. Two-dimensional SU(2) Yang-Mills
on a closed surface of genus `g`, in the zero-area (topological) limit, has `Z = sum over irreducible representations
of (dim)^(2 - 2g) = sum_{n >= 1} n^(2 - 2g) = zeta(2g - 2)`. The SU(2) Witten zeta function is the Riemann zeta function.
The centre element `-1` acts on the representation of dimension `n` by `(-1)^(n+1)`. So the electric sector `e = 0`
collects the odd `n` and `e = 1` the even `n`. Normalisations common to both sectors cancel in every ratio.

**The Lean** (section 4; `s = 2g - 2 > 1`, i.e. `g >= 2`):
- `Ze1_eq`: `Z_{e=1} = 2^-s Z` [Lean].
- `Ze0_eq`: `Z_{e=0} = (1 - 2^-s) Z` [Lean].
- `zeta_re_eq`: `Z = re zeta(s)`, Mathlib's `riemannZeta` [Lean].
- `sector_dom_iff`: `mu Z_{e=1} <= Z_{e=0}` exactly when `mu + 1 <= 2^s` [Lean].
- `twist_ratio`: `Z_tw/Z = 1 - 2^(1-s)` [Lean]. As analytic functions this is `eta(s)/zeta(s)`. The nontrivial zeros
  of zeta are zeros of `eta` too and cancel [classical].

**What it shows.**
- Even where zeta *is* the partition function, the O1-type quantity (a sector ratio) contains no zero of zeta. It is one
  Euler factor, at the prime 2, because the centre `Z_2` splits representations by parity. Every statement about the
  zeros, RH included, is irrelevant to it.
- With area `A > 0` the torus gives `Z(A) = sum_n exp(-A (n^2 - 1)/8)` (a theta function), whose Mellin transform in
  `A` is `Gamma(s) zeta(2s)` up to elementary factors. Riemann's proof of the functional equation runs exactly through
  this theta function [classical]. So RH is equivalent to a statement about the area dependence of 2D SU(2) Yang-Mills
  on the torus (the zeros of a Mellin transform of its partition function) [classical, as a reformulation]. The sector
  ratios split the same way: in Mellin space `4^-s` against `1 - 4^-s` [classical]. The 2D model is the one place where
  a coupling to zeta exists, and there the O1-type statement holds unconditionally (exact solution; join loss computed in
  `OPEN-STEPS-DMP.md` 1(c)) [numerical, classical]. RH is not needed there either.
- 2D has no outside (independent plaquettes). The four-dimensional for-all over outsides, which is the hard part of
  O1, has no counterpart on the zeta side at all.

## 5. The missing claim, named

`ZetaCoupling p0 p1 mu` [Lean definition; content open]: one bound `B` on the sector ratio `p1/p0`, valid for every
outside, with `B <= 1/mu'` for some `mu' > mu` as soon as RH holds.
- `o1_of_coupling`: the coupling and RH give O1 [Lean].
- `coupling_of_o1`: O1 gives the coupling, with RH unused [Lean].

So the exact intermediate claim that no known result supplies is a bound on the hand-over box's sector ratio, uniform
over outsides, by a quantity of zeta's zeros that RH controls. It is no easier than O1, because O1 alone implies it. No
known theorem relates four-dimensional SU(N) Wilson weights at a box of fixed physical size to zeros of zeta or of
Dirichlet L-functions [classical, to the best of the literature check in section 7].

## 6. Circularity check

- **In Lean: no circle.** No file under `ProofPhase/GRH/`, `ProofPhase/API/GRH.lean` or `ProofPhase/Unified/GRH.lean`
  mentions `YMOneBox`, `CostAboveFloor`, the hand-over or any `Crossover` module (checked by grep). The GRH side imports
  only the form layer (`Unified/Ledger.lean`, `Unified/Transport.lean`) and its own files. `GRH/OneBoxCert.lean` uses
  the transport theorem's sign part, a proved form-layer theorem with no open hypothesis [Lean].
- **In the external slots: none.** `ExtRH` and `ExtDirichletGRH` are Mathlib-level statements about zeta and Dirichlet
  L-functions. They are named hypotheses here, never derived from a Yang-Mills statement.
- **In the readings: one shared-shape risk, not a circle.** The project reads both GRH and O1 through the same encoder
  (`GRH-LENS.md` 6). That shared vocabulary is a reading. It must not be mistaken for a logical link: the half-turn and
  positivity are symmetries and signs (`GRH-LENS.md` 6.3), and they carry no margin from one problem to the other
  (section 3 here).
- **A circle to avoid in the paper.** It would be circular to justify O1 by "the floor is at least the error bar" and
  then to justify the error bar by O1's rate. The settle theorem takes the floor as a hypothesis (`PREP.md`, the floor
  entries) [Lean]; that keeps it honest.

## 7. Literature (search on 2026-11-24 plus recall)

- **No established link between RH/GRH and the 4D mass gap** [classical; a web search found none in refereed sources].
  Several self-published preprints (2025 to 2026) assert one. None is refereed, and none gives a proof of either problem.
  They are not used.
- **2D Yang-Mills and zeta** [external]: Witten, "On quantum gauge theories in two dimensions", CMP 141 (1991): volumes
  of moduli spaces and zero-area partition functions through `sum (dim R)^(2-2g)`; for SU(2) this is `zeta(2g - 2)`
  (also: Zagier, Witten zeta functions; recent work on 2D Yang-Mills and resurgence uses zeta values at even integers
  only).
- **Statistical-mechanics systems with zeta as partition function** [classical, recalled]: Julia's primon gas, the
  Bost-Connes system (phase transition at `beta = 1`), Knauf's number-theoretic spin chain. None has an outside or a
  gauge structure, and in none does RH become a mass-gap statement.
- **Lee-Yang and de Bruijn-Newman** [classical, recalled]: RH is equivalent to `Lambda <= 0` for the de Bruijn-Newman
  constant, and `Lambda >= 0` (Rodgers-Tao 2018). This is a zeros-on-a-line statement in the Lee-Yang sense
  (`GRH/LeeYang.lean` in-project), not a gap.
- **Connes, Connes-Consani** [external, pointer]: Weil positivity as a trace-formula positivity; proved for test
  functions supported in a small interval (the archimedean place). This is the strongest "positivity from the median"
  result known, and it is a sign, not a margin.
- **The arithmetic mass gap** [classical, recalled]: Selberg's eigenvalue conjecture (`lambda_1 >= 1/4` on congruence
  surfaces) is the closest arithmetic analogue of a spectral gap. It follows from Ramanujan-Petersson at the infinite
  place, not from GRH; the best known bound is `975/4096` (Kim-Sarnak). Even in arithmetic, a gap is not a consequence
  of GRH.

## 8. Status table

| claim | status |
|---|---|
| O1 is the uniform ratio bound; O1 is positivity with a strict margin | [Lean] |
| the electric cost is `log(p0/p1)` | [Lean] |
| "GRH implies O1 on every card input" is equivalent to "GRH is false" (RH, Dirichlet GRH, card form) | [Lean] |
| pair model: GRH card open step and conclusion hold, YM card open step fails | [Lean] |
| GRH-side positivity has margin exactly 0 at the closure of a finite model | [Lean] |
| positive sector weights with O1 false | [Lean] |
| 2D SU(2): sectors `2^-s zeta`, `(1 - 2^-s) zeta`; sector domination iff `mu + 1 <= 2^s`; twist ratio `1 - 2^(1-s)`; `Z = re zeta(s)` | [Lean] |
| 2D SU(2) zero-area partition function is `zeta(2g - 2)` | [external] (Witten 1991) |
| RH as a statement about the area dependence of 2D SU(2) on the torus (theta, Mellin) | [classical] |
| the coupling and RH give O1; O1 gives the coupling | [Lean] |
| growing support is nested restriction; the margin is monotone | [Lean] |
| O1 at every tick drives the carried Szego margin to zero; a uniform margin excludes O1 per tick | [Lean] |
| multiplicative transport (lower bound on the factor) and O1 (upper bound) are independent | [Lean] |
| bounded Birkhoff spread on the two-sector cone and O1 are independent | [Lean] |
| Szego steps are SU(1,1) isometries (`Delta = infinity`, also at the start `{infinity, 2, 3}`) | [classical] |
| a uniform margin of Weil's form is false (purely atomic zero measure; Szego-Kolmogorov-Krein; Slepian) | [classical] |
| the coupling itself for 4D SU(N) at the hand-over box | [open]; no known result |
| GRH (all three forms) | [open] |
| O1 | [open] |
| no circularity between the GRH side and O1 in Lean | [Lean] (by imports and grep) |
| "GRH's irreducibility supplies the floor" | fails as a derivation; [reading] as a shared shape |

## 9. Files

- `docs/mass-gap/formal/ProofPhase/Unified/GRHToO1.lean` (new).
- `docs/unified/grh-to-o1-axioms.sh`, `docs/unified/grh-to-o1-axioms.log` (new).
- Read, not changed: `API/GRH.lean`, `API/YangMills.lean`, `Unified/GRH.lean`, `Unified/YangMills.lean`,
  `Unified/GRHLens.lean`, `GRH/TieIn.lean`, `GRH-LENS.md`, `OPEN-STEPS-DMP.md`, `TRANSPORT.md`, `PREP.md`.
