# The three open steps, read natively in DMP: starting points and simplifications

Status: 2026-11-23. Exploratory round, not a proof round. Nothing here proves an open step, and none of the three is
stated as proved. Sources: the owner's readings in `docs/mass-gap/weak-coupling/PREP.md` (from "GRH reads the ledger in
two separate ways" to the end), `UNIFIED.md`, `ENCODER.md`, `GRH-LENS.md`, `SUN-PRIMES.md`, `BLOWUP.md`,
`docs/OPEN-QUESTIONS-DMP.md`, `docs/SYNTHESIS-DMP.md`, and the DMP spec (read only).

Third-layer check: `open_steps_check.py`, `open_steps_check.log`. CPU only, seconds, no saved data needed.

Status marks: **Lean** (proved in this repository), **classical** (known mathematics, recalled, not re-proved here),
**recalled** (classical but cited from memory and not re-read in this round; to be checked before the paper uses it),
**external** (proved elsewhere, an audit item), **numerical** (checked by the script), **reading** (an identification
with DMP vocabulary, not a theorem), **open** (not proved by anyone), **fails** (the lead does not give what is asked).

---

## 0. In plain words

The form layer is done: one ledger, one encoder on the sphere, the half-turn, every SU(N). Each problem keeps one open
step in its content. This round asked, for each step, where DMP's own picture suggests starting, and whether anything
makes the step smaller.

**Yang-Mills (O1).** The best start is the **handshake in series**. Do not try to lift one box from the proved 0.881 to
the needed 1.913. Take three hand-over boxes in a row, each sharing a face with the next. Costs then add, and the step
becomes two smaller statements:
- each hand-over box sits on the electric side;
- the loss at each shared face (the handshake) stays below 0.244.

The loss at a face has an exact DMP meaning: it is the **tail of remnants**, the higher sectors that do not compose
cleanly. In the one exactly solvable confining model, two-dimensional SU(2), the loss is 0.13 at the hand-over and at
most 0.19, with a margin under 0.244 [numerical]. There, three hand-over boxes clear the floor at every coupling and in
the continuum limit. That model has no outside, so it calibrates the arithmetic and proves nothing about four
dimensions. Earlier rounds found a second partial simplification: the box meeting its own mirror image (reflection
tiling). It removes the "for every outside" quantifier, at the price of a global free energy. **Verdict:** a real
reformulation that splits O1 into a side and a join loss. It does not shrink the difficulty, which is still a uniform
two-box bound.

**GRH sign.** The best start is the **one case where the sign is a theorem from the prime side alone**: curves over a
finite field. There the project's ledger appears exactly:
- the existence space is finite (2g zeros);
- there is a real tick (the Frobenius step, log q);
- the Szego recursion closes with |k_2g| = 1 after steps all inside the disk.

The check confirms this from point counts alone on four genus-2 curves; a fake off-circle atom set gives |k| = 1.21 > 1
[numerical]. Weil's proof shows which DMP ingredient does the work: a **handshake of the curve with itself** (the
surface C x C, the Frobenius graph as the shared root) plus a positivity there (the Hodge index). The integrality route
(Stepanov's counting) also works there, because point counts are integers at a fixed tick. **Verdict:** no
simplification over the integers. The step becomes precise: supply a tick and a self-product with a positive pairing.
That is a known open programme (the square of Spec Z), not a smaller statement. The first rung (the real place alone,
before the prime 2 enters) is already proved (in-project, recalled). Pairing an L-function with its dual (Rankin-Selberg)
gives positive prime-side coefficients and so zero-free regions, but with slack shrinking like 1/log t, never the line.

**NP vs coNP crossing cost.** The best start is a known theorem of exactly the handshake shape. **Lifting**
(Garg-Goos-Kamath-Sokolov 2018, recalled) splits each variable between two parties, so it exists only as their
agreement. One party alone sees nothing, which is the project's finding that a one-boundary encoder is lossless. The
theorem turns the one-boundary cost (resolution width, which the encoder explains) into a cutting-planes size cost for
the lifted formula. **Verdict:** a genuine simplification for one class. For gadget-composed formulas the cutting-planes
crossing cost reduces to a resolution width bound, which is in reach. It does not cover the unlifted constant-width
formulas of the project's interface question, or Frege.

**Shared simplification?** **No single one.** The two-box handshake is the shared starting point: in all three problems
every known partial result is a two-copy construction (the box with its mirror or neighbour, the curve with itself,
the variable split between two parties). But the three theorems are different mathematics, and in none does the
handshake supply what is open. Integrality is the shared location of the cost, not a simplification. The common
pattern [reading]: the handshake simplifies exactly where the **tick is discrete and the pair is finite**:
- 2D gauge theory: independent plaquettes;
- function fields: Frobenius;
- lifted formulas: a finite gadget.

The open steps sit where one of these is missing:
- 4D Yang-Mills: the outside is unbounded;
- arithmetic over Z: there is no tick;
- Frege: lines are unbounded formulas.

**Under the construction principle** (existing tools tied by top theorems; each step's (c+) part):
- **Yang-Mills:** the tools (reflection positivity, chessboard, Tomboulis-Yaffe, Birkhoff-Hopf, the ledger) share one
  hyperbolic distance, the encoder cost. No existing result supplies the input number.
- **GRH:** Weil's criterion and Verblunsky share the positivity of one Toeplitz form. The external RH and Dirichlet
  proofs cover zeta and Dirichlet completely, once tied in by the easy direction of Weil's criterion (an audit and a
  small Lean lemma). Nothing covers the step beyond Dirichlet.
- **NP vs coNP:** interpolation and lifting share low communication across a split. They cover cutting planes on lifted
  formulas.

---

## 1. O1 (Yang-Mills): the encoder of the hand-over box

**Exact form** (`ENCODER.md` 6, `GRH-LENS.md` 6.4 and 9.1). At the hand-over box of fixed physical size, for every
well-defined outside, `c = Z_tw/Z >= c0 > (mu_4 - 1)/(mu_4 + 1) = 0.743`. Equivalent forms:
- `F_tw <= 0.297`;
- `F_e > log mu_4 = 1.913`;
- `mu_4 Z_{e=1} <= Z_{e=0}`.

All are Lean equivalences (`ymOneBox_iff_refl`, `oneBox_twist_form`, `oneBox_sector`). Proved per finite lattice for
every SU(N): `0 < c < 1` (`SUNTwistWilson.lean`, Lean). The self-dual hand-over gives only `c = sqrt 2 - 1 = 0.414`
(`handover_refl`, Lean).

### (a) The step in DMP's own terms

| DMP term [reading] | exact counterpart | status of the counterpart |
|---|---|---|
| G0 (the root form) | the positive, reflection-positive Wilson weight `e^{-S} >= 0` | Lean (RP, `M1/UVTVOS.lean`) |
| DB | the boundary (collar) of the hand-over box, where only the centre label is seen | Lean (centre labels, `General/Centre.lean`) |
| the encoder at the DB | `c = Z_tw/Z`, a point of the Schur hemisphere; cost = hyperbolic distance from `c = 0` | Lean (`elec_cost`) |
| ODP / pressing | box by box up to physical size `l`; the hand-over set is closed upward | Lean (`flux_superadd_iter`) |
| act | the centre twist on a plane; as a model, tunnelling between centre sectors, `elec(c) = e^{-T gap}` | Lean (twist); numerical (`tunnel_check`) |
| handshake (two nodes agree on a shared root) | two neighbouring boxes share the flux label of their common face; their departure from independence is a determinant | Lean (`exists_sheet_both_sides`, `twoBox_defect`) |
| tail of remnants | what a join of two boxes does not carry: the loss `l = F_e(L1) + F_e(L2) - F_e(L1 + L2)` | definition here; numerical in 2D (section 1(c)) |
| quantum of assertion | at least one sheet for a flux-carrying outside; `abs(Q) >= 1/2` for a twist with nonzero Pfaffian | Lean (sheet); classical (Bogomolny) |
| tick | the per-step floor: path entropy `log mu_4` (or the chain floor `2C`) | Lean (`tube_threshold`, `ym_flux`) |
| settling at known error rates | cost above floor gives a rate; measurement only refutes (provability table) | Lean (`rate_of_costAboveFloor`); design rule |

**Restated.** At the DB of the hand-over box, for every outside, the encoder sits on the electric side of the half-turn
axis, at hyperbolic distance at least one tick (`log mu_4`) from the lossless point. Proved: it is at least 0.881 from
the lossless point on one side or the other (`max(F_e, F_tw) >= 0.881`, Lean). Open: the side, the extra distance, and
the for-all. **open**

### (b) Most promising starting point: the handshake in series

Three hand-over boxes in a row, each joined to the next through one shared face. Costs add along the hyperbolic line,
so three lossless boxes give 2.644 > 1.913 (`three_steps_clear`, Lean). With a loss `l` per join, three suffice while
`l < 0.244` and four while `l < 0.403` (`GRH-LENS.md` 6.4, Lean for the arithmetic).

Why this start:
1. **It reuses the proved number.** It needs no new one-box quantity; the 0.881 of `HandOver.lean` is the unit.
2. **It is the owner's handshake, literally.** The join is two boxes agreeing on the label of their common face, and the
   join loss is a two-box quantity: the remnant tail at the shared root.
3. **The arithmetic has room.** In the one exactly solvable confining model the join loss is well below the threshold
   (section 1(c)). So the series route is not killed by its own bookkeeping.
4. **It matches what pressing does.** The hand-over set is closed upward (`flux_superadd_iter`, Lean). Three boxes in a
   row is a box of size 3L, still a hand-over point.

### (c) Simplifications found

**S1. The series split** [reading for the route; Lean for the arithmetic]. O1 at box 3L follows from two statements:
- **(side)** at the hand-over box `L_h`, `F_e(L_h) >= 0.881` (electric side), uniformly over outsides;
- **(join)** the join loss is below 0.244, uniformly over outsides.

How much it removes: the quantitative distance from 0.881 to 1.913 is no longer asked of one box. It is moved into the
join loss, a two-box quantity with a margin. What it does not remove: both parts still carry the for-all over
outsides. The side is the open part 1 of `GRH-LENS.md` 6.4 (the hand-over gives one of `F_e`, `F_tw`, not which). So
this is a reformulation into two smaller-looking statements, not a reduction to a proved one.

**Calibration in two dimensions** (`open_steps_check.py` part A) [classical formulas; numerical]. On a 2D torus of area
`A` the SU(2) theory is solved by characters:
- `Z_e0 = sum over integer spins of r_j^A` and `Z_e1 = sum over half-integer spins of r_j^A`;
- `r_j = I_{2j+1}(beta)/I_1(beta)`, with the heat kernel in the continuum.

There is no outside, since the plaquettes are independent.

| beta | area ratio O1/hand-over | join loss at the hand-over (2 boxes) | max join loss, areas 0.05 to 6 `A_h` | 3 boxes clear O1 |
|---|---|---|---|---|
| 1.0 | 2.28 | 0.083 | 0.100 | yes |
| 2.3 | 2.32 | 0.109 | 0.139 | yes |
| 8.0 | 2.35 | 0.130 | 0.183 | yes |
| continuum | 2.356 | 0.132 | 0.189 | yes |

What the numbers say:
- The join loss is positive, but it stays below 0.244 at every coupling and in the continuum limit.
- Its source is exactly the remnant tail. If only the two lowest sectors (spin 0 and 1/2) existed, `F_e` would be
  linear in area and the loss zero. The loss comes entirely from spin 1, 3/2 and above.
- So in this model the owner's "the bulk carries only the tail of its remnants" is the join loss, and the tail is small
  enough.

Care points:
- 2D has no outside and no running coupling, so the calibration says nothing about four dimensions. It shows only that
  the series route is not too tight in a model where confinement is exact.
- The 2D "box" is an area. The 4D hand-over box is a volume with a collar.

**S2. The box meeting its own mirror** (already in-project: `weak-coupling/attempts/lead/NOTE.md` 2,
`attempts/positivity/NOTE.md` 4.2) [classical: chessboard estimates, Froehlich-Israel-Lieb-Simon, recalled].

What it does:
- Tiling the torus by reflected copies of the box replaces every outside by mirror images of the box itself. It is a
  handshake of the box with its own reflection.
- Tomboulis-Yaffe (1985, recalled) use this to bound Wilson loops by the electric-flux (twist) free energy on tori.

How much it removes: the for-all over outsides. The project's earlier rounds found the price:
- the disseminated quantity is a global free energy, so the cross-scale problem returns inside it;
- reflection positivity sees reflection-symmetric states, not worst-case boundaries, so the natural target becomes
  torus decay (`LevelDecay`), not the boundary-uniform statement;
- every inequality built only from this positivity also holds for U(1), so it cannot by itself produce confinement (the
  Cartan identity, `attempts/positivity/NOTE.md` 4.2).

**S3. Integrality.** **fails** (`GRH-LENS.md` 9.2). An action floor on twists pushes `F_tw` up, which is the wrong side
for O1. No new finding here.

**Net:** S1 is new as a split with a calibrated margin; S2 is known in-project; S3 fails. The difficulty that remains is
one uniform two-box bound.

### (c+) Tools that click, the tying theorem, the shared property (construction principle, PREP last entry)

**Existing tools that click here:**

| tool | what it supplies | mark |
|---|---|---|
| reflection positivity and chessboard estimates (Froehlich-Israel-Lieb-Simon 1978) | outsides replaced by mirror copies; torus bounds | classical; RP itself Lean |
| Tomboulis-Yaffe (CMP 100, 1985) | small electric-flux (twist) free energy on tori implies an area law | external, recalled |
| Martinelli-Olivieri, Dobrushin-Shlosman finite-size criteria | one-box mixing implies the infinite-volume property (spin systems) | classical |
| Birkhoff-Hopf projective contraction | a positive map with image cone of finite Hilbert diameter `Delta` contracts by `tanh(Delta/4)` | classical |
| Balaban; the external continuum construction | the ultraviolet side | external, audit item (`paper` III.9) |
| de Forcrand, von Smekal and others: lattice measurements of electric-flux free energies in SU(2) | evidence that `F_e(L)` grows with `L` | external numerical, recalled; refute-only |

**Tying theorem and shared property.**
- The ledger's `rate_of_costAboveFloor` (Lean) tied to Birkhoff-Hopf.
- The shared property is **one distance**: the Hilbert projective metric on the two-sector cone is the hyperbolic
  distance that the encoder cost already is (`elec_cost`, Lean; `GRH-LENS.md` 6.5).
- Birkhoff-Hopf turns a bound on that distance into a contraction, and the ledger turns the contraction into a rate.
- The series split S1 is stated in the same distance: costs add along the hyperbolic line, and the join loss is its
  defect.
- So the tools already share one property, and the form layer can tie them without new machinery.

**What the best existing content covers, and the audit it needs:**
- **Tomboulis-Yaffe** covers the step from a small twist free energy on tori to confinement (an area law). It does not
  give the gap, and its input is the O1-type number itself.
  - Audit: re-read CMP 100 (1985).
  - Check that its torus quantity matches `F_tw` here.
  - Check that it uses only reflection positivity for the Wilson action (site and link reflections).
- **Finite-size criteria** cover "one box implies everything" for spin systems. For the gauge chain the project already
  has its own Lean version (`phys_rate_of_uniform`, the assembly), so nothing needs adopting there.
- **Not to be used:** the 2007 attempt at a small twist free energy for all beta (Tomboulis, arXiv:0707.2179) is not
  regarded as complete. Ito-Seiler argue that its method would also confine U(1) (in-project,
  `attempts/positivity/NOTE.md` 4.3).
- **Left for the content:** the input number (the side and the join loss, equivalently a disseminated twist free
  energy). No existing solution covers it. Lattice measurements are evidence only.

### (d) A first construction step for the next round

- **CPU (refute-only, as the provability table allows).** Measure the join loss `l(L) = 2 F_e(L) - F_e(2L)` on `L^4`
  tori at one beta near the hand-over, with the `F_e(L) = log((1 + r_L)/(1 - r_L))` pipeline of `ONEBOX-CHECK.md`
  (section on the cubic geometry), at `L = 2, 4` or `3, 6`. A certified `l > 0.403` at the hand-over would refute the
  series route at that size; `l < 0.244` would only be consistent with it.
- **Lean (cheap).** State `JoinLoss` as a named hypothesis: `F_e(L1 + L2) >= F_e(L1) + F_e(L2) - l` with `l < 0.244`.
  Together with an electric-side hypothesis at `L_h`, derive `YMOneBox` at `3 L_h` from `three_steps_clear` and
  `flux_superadd_iter`. This replaces O1 in the ledger by the two named pieces, so a later round can attack them
  separately.

---

## 2. The GRH sign beyond Dirichlet

**Exact form** (`GRH-LENS.md` 1 and 7; `UNIFIED.md` 3.2; `ENCODER.md` 6). Every scale step's reflection coefficient
satisfies `abs(k_m) <= 1` (`ScaleSign`, equivalently every finite section positive, `scaleSign_iff`, Lean). It must be
shown from the primes, the characters and the real place alone. Zero slack: the cost equals the floor, and the margin is
about `1e-9` per step (`INDUCTION.md`). **open** beyond Dirichlet. RH and Dirichlet GRH themselves are proved in Lean by
others (external).

### (a) The step in DMP's own terms

| DMP term [reading] | exact counterpart | status |
|---|---|---|
| G0 | Weil's positive form, one form for all scales, not assembled place by place | Lean (`GRH/Transfer.lean`: no subset assembly) |
| DB | the boundary of a scale cell on the grid; the encoder there is the Szego coefficient `k_m` | classical; Lean for lag encoders |
| ODP / pressing | add one scale cell at a time; the prime power `n` enters at lag `log n` | Lean (ledger); numerical (`INDUCTION.md`) |
| act | an impulse of the explicit formula at lag `log n`, weight `Lambda(n)/sqrt n` | classical |
| handshake | `f` paired with its mirror `f~` in `W(f * f~)`; for an L-function `pi`, `pi` paired with its dual `pi~` (Rankin-Selberg); over a finite field, the curve with itself (`C x C`) | classical |
| tail of remnants | each zero `rho` leaves `x^rho`; GRH = every tail of size `x^{1/2}` (von Koch) | classical |
| quantum of assertion | integer lags (`n` an integer), integer multiplicities, the integer zero count `N(T)` | classical |
| tick | the grid step `eps`; over `F_q` the Frobenius step `log q`; over Z the floor is 0 | Lean (floor 0, `UNIFIED.md` 6); classical |
| settling at known error rates | Turing's method certifies finite heights; with `kappa = delta` exactly there is no exponential rate (critical case) | classical; PREP reading |
| closure (finite existence space) | `abs(k_N) = 1` at `N` = number of atoms | Lean (`atoms_on_circle`); numerical (`closure.py`) |

**Restated.** At every DB of the scale ladder the encoder stays in the closed disk (the hemisphere of the sphere
picture), and the only input allowed is the prime side and the real place. Positivity says "in the disk", never "where"
(Verblunsky). So the step is purely a sign, with no distance to gain. **open**

### (b) Most promising starting point: the function-field instance

Curves over a finite field are the one case where the step is a theorem built from the prime side alone (Weil 1948,
classical). There the project's finite model is not a truncation; it is exact:
- `Z(C, T) = P(T)/((1 - T)(1 - qT))` with `deg P = 2g`. The existence space is finite: `2g` atoms on the circle (after
  normalising by `sqrt q`), repeating with the tick `log q` in the imaginary direction.
- Their moments come from point counts `N_m = q^m + 1 - sum alpha_i^m` (the prime side), and only `N_1, ..., N_g` are
  needed (rationality).
- The Szego recursion has `abs(k_m) < 1` for `m < 2g` and closes with `abs(k_2g) = 1`: both of the owner's readings
  ("spanned exactly as described" and "causality at every scale"), as a theorem.

**Check** (`open_steps_check.py` part B) [numerical; Weil's theorem]. Four genus-2 curves over `F_7, F_11, F_13, F_31`:

| p | `abs(k_1..k_4)` |
|---|---|
| 7 | 0.283, 0.204, 0.658, 1.000000000000 |
| 11 | 0.075, 0.577, 0.116, 1.000000000000 |
| 13 | 0.277, 0.083, 0.933, 1.000000000000 |
| 31 | 0.314, 0.638, 0.453, 1.000000000000 |

- All four atoms are on the circle in each case.
- Control: a fake atom set with one quartet off the circle (`abs(beta) = 1.15, 1/1.15`) gives `abs(k_4) = 1.21`, an
  overdrawn step, and the recursion still closes with `abs(k_6) = 1`. That is the separation `closure.py` found for zeta
  (the closure holds off the line; the bound fails).

Why this start: it shows which DMP ingredients do the work when the sign is true. There are two classical proofs.
- **The handshake.** Weil's proof uses the surface `C x C`: two copies of the curve. The diagonal and the graph of
  Frobenius are the shared roots, and the Hodge index theorem (Castelnuovo-Severi) gives the positivity [classical]. In
  the owner's words: two nodes (two copies of the existence) agree on a shared root (the Frobenius graph), and the
  positivity of that agreement is the sign.
- **The quantum and tick.** Stepanov's method (Bombieri's form) builds an auxiliary function vanishing to high order at
  the rational points. Dimension counting (integers, Riemann-Roch) then bounds the integer point count [classical]. It
  needs the fixed tick `q`: the Frobenius is an algebraic map.

### (c) Simplifications found

**None that makes the step smaller over the integers.** Plainly:
- **The first rung is free** (already in-project: `INDUCTION.md`, P(0)). For support up to `(1/2) log 2`, before the
  prime 2 enters, positivity is the real place alone. It is proved (Yoshida 1992 for small supports; Connes-Consani 2021
  up to this support; recalled). This matches the owner's "the base prime is 2". It removes one rung of an infinite
  ladder.
- **The handshake over Z** is the known missing object [classical programme]: a self-product "Spec Z x Spec Z" with a
  Hodge-index positivity (Deninger; Connes-Consani's arithmetic site; Haran). Naming it as the two-box handshake is
  exact, but the statement does not get smaller. It becomes "build the square and its positive pairing".
- **Rankin-Selberg as a handshake**, recalled:
  - Pairing `pi` with `pi~` gives `L(pi x pi~, s)`, whose prime-side coefficients are `abs(a_pi(p))^2 >= 0`, positive
    on the prime side. With de la Vallee Poussin's positive polynomial this gives zero-free regions for general
    L-functions, `sigma > 1 - c/log(...)` (with the Siegel-zero caveat). That is slack shrinking like `1/log t`, the
    same non-uniformity `GRH-LENS.md` 9.3 found.
  - What it removes: nothing of the sign. Prime-side positivity of the paired object controls the edge of the strip,
    not the line.
- **Integrality** works only with a tick. Over `F_q` the point count is an integer at a fixed scale `q`; over Z there is
  no Frobenius and no fixed tick (floor 0). The integer lags `log n` are present, but they are not a scale step of one
  map.
- **The margin is monotone.** The least eigenvalue of the form on support `[-X, X]` is non-increasing in `X` (a larger
  space, an infimum over more) [classical, elementary]. So a step can never recover margin lost earlier: there is no
  slack to propagate, and no hand-over point exists (PREP, the hand-over entry).

So the function-field instance does not simplify; it makes the target precise. Over Z, DMP would have to supply a tick
(a scaling action with discrete steps, Connes's scaling action being the standard candidate) together with a positive
two-copy pairing. Both are the content of the open step.

### (c+) Tools that click, the tying theorem, the shared property

**Existing tools that click here:**

| tool | what it supplies | mark |
|---|---|---|
| Weil's explicit formula and Weil's criterion (RH for a family iff Weil's functional is positive) | the bridge between zeros and the prime side | classical |
| Verblunsky, Geronimus, Szego | positive measure iff every reflection coefficient in the disk; the step factors multiply to one global quantity | classical |
| Yoshida; Connes-Consani | positivity for support up to (1/2) log 2 (the first rung) | external, recalled |
| the Lean proofs of RH and Dirichlet GRH by others (2026-11-20) | zeros on the line for zeta and Dirichlet L-functions | external, audit item |
| Weil (curves), Deligne (varieties over `F_q`) | the full sign in the function-field world | classical |
| Rankin-Selberg, de la Vallee Poussin | zero-free regions beyond Dirichlet | classical |

**Tying theorem and shared property.**
- Weil's criterion tied to Verblunsky's theorem.
- The shared property is **positive-definiteness of one Toeplitz (convolution) form**:
  - Weil's functional is that form on test functions;
  - Verblunsky reads its positivity as `abs(k_m) <= 1` at every step (`ScaleSign`, `scaleSign_iff`, Lean).
- The form layer already ties them.

**What the best existing content covers, and the audit it needs:**
- **For zeta and Dirichlet L-functions, the external proofs cover the whole sign.** By the easy direction of Weil's
  criterion, zeros on the line imply that Weil's functional is positive, hence `ScaleSign` on every grid section.
  - Audit: read the external proofs' top statements and `#print axioms`.
  - Formalise the easy direction of Weil's criterion as the tying lemma (zeros on the line imply positivity), and check
    whether the repository already has it. This would make the Dirichlet column of the ledger a theorem by others' content
    plus our tie.
- **The independent positivity route** (without using the zeros) stays open even there; it is the paper's own claim
  structure, not a gap in the content.
- **Beyond Dirichlet** no existing solution covers the step over Z. The function-field theorems cover the analogue
  completely and are the model, not a part of the step.

### (d) A first construction step for the next round

- **Lean (vacuity check of the GRH instance).** Instantiate `ZeroModel` and `ScaleSign` (`Unified/GRH.lean`) with a
  function-field atom model: `2g` atoms of modulus 1, uniform weights. The Hasse-Weil bound `abs(alpha_i) = sqrt q` is a
  named external hypothesis (Weil's theorem is not in Mathlib, recalled). Derive the closure at `2g` and `ScaleSign` for
  `m < 2g` from `atoms_on_circle`. This shows that the GRH column of the ledger is inhabited by a true theorem case with
  a genuine tick, which the zeta grid model cannot show.
- **CPU (optional).** Extend part B to count `N_3, N_4` directly over `F_{p^3}, F_{p^4}`. This checks that the moments
  beyond `g` agree with rationality, i.e. that the finite existence space is spanned exactly by the prime side.

---

## 3. The crossing cost (NP vs coNP)

**Exact form** (`ENCODER.md` 6, `GRH-LENS.md` 5 and 9.4, `UNIFIED.md` 3.3).
- A one-boundary encoder is lossless: the crossing label passes at factor 1, and a cutting-planes line names it at
  factor 1 (`thr_share_one`, Lean).
- The cost must come from a step that combines two lines: every cutting-planes refutation contains a rounding of a
  combination of at least two lines, when the axioms have a fractional solution (`refutation_needs_pair`,
  `CPPairs.lean`, Lean).
- Whether that step has a factor finitely below one, for strong systems (cutting planes at constant width, Frege), is
  `CrossingCost`. **open**

### (a) The step in DMP's own terms

| DMP term [reading] | exact counterpart | status |
|---|---|---|
| G0 | the unsatisfiable formula; non-existence certified by a refutation | Lean (`complete`, `refutable_iff`) |
| DB | a cut of the variables (`A(x, y)` and `B(x, z)`); the encoder is the share of costly lines a restriction keeps | Lean (`survShare`, `split_unsat_iff`) |
| ODP / pressing | restrict one literal at a time | Lean (ledger) |
| act | a derivation step; the costly act is the rounding (Chvatal-Gomory cut) | Lean (`half_breaks_rounding`) |
| handshake | the rounding of a combination of two lines; in lifting, a variable split between two parties | Lean (`refutation_needs_pair`); classical (lifting) |
| tail of remnants | the intermediate lines carried; the largest is the width; size and width are tied | Lean (`size_width_exp`) |
| quantum of assertion | one costly line left at the end; integrality of the variables, which rounding uses | Lean (`CrossingCost`); classical |
| tick | floor 0 | Lean (`UNIFIED.md` 6) |
| settling at known error rates | traversal of the route always decides; the question is its length | Lean (completeness); open (length) |

**Restated.** At a DB the one-boundary encoder is lossless (`c = 0`, factor 1). The cost, if any, is paid at a
two-line handshake: the rounding, which asserts that a combination of two lines is an integer. It is the quantum of
assertion acting on a pair. **open**

### (b) Most promising starting point: lifting

A known theorem has exactly the handshake shape (Garg, Goos, Kamath, Sokolov, "Monotone circuit lower bounds from
resolution", STOC 2018; recalled):
- **The statement.** If an unsatisfiable CNF `F` needs resolution width `w`, then the composed formula `F o g`, with an
  index gadget `g` of polynomial size, needs cutting-planes refutations of size `n^{Omega(w)}`. The same holds for any
  system whose lines have cheap real communication protocols.
- **The gadget is a handshake.** Each variable `x_i` is replaced by a gadget: one party holds a pointer, the other a
  table, and `x_i` is defined only by both. One party alone sees a uniformly random value. That is exactly the
  project's finding that a one-boundary encoder is lossless (`c = 0`), now by design.
- **The cost is paid at the shared root.** A cutting-planes line splits across the two parties into a cheap real
  communication protocol (Krajicek 1998, Pudlak 1997; recalled; in-project as feasible interpolation,
  `CP-DUALITY.md`). A short refutation of `F o g` would therefore give a cheap protocol for the search problem of
  `F o g`. Lifting shows that such a protocol costs at least the resolution width of `F`.

Why this start:
- it is the only known theorem that converts the one-boundary cost the encoder explains (resolution width, which the
  ledger already handles: `size_width_exp`, Lean side) into a two-line cost for cutting planes;
- it does so through exactly the structure the owner describes: two nodes, one shared root, nothing crossing without
  the handshake.

In the DMP spec's own terms (Axiom 1 and C22: "proven" needs two independent witnesses), the lifted variable is a
two-witness value [reading].

### (c) Simplifications found

**For the class of lifted formulas, yes:**
- **What it removes.** The cutting-planes crossing cost of `F o g` reduces to a resolution width lower bound for `F`.
  Width lower bounds are classical (Tseitin on expanders, random 3-CNF, pigeonhole: linear width; Ben-Sasson-Wigderson)
  and their size consequences are on the Lean side.
- **How much.** The whole cutting-planes step, for every formula of the form `F o g` [recalled; external theorem].
  Cutting-planes lower bounds were already known for specific formulas (clique-colouring, random `Theta(log n)`-CNF,
  in-project `CP-DUALITY.md`). Lifting adds a general reduction: any width-hard formula, once lifted.

**What it does not cover:**
- **Unlifted constant-width formulas** (the project's interface question at width 3, `CP-DUALITY.md` 4). A lifted 3-CNF
  has width about `3 x (gadget size)`. With a polynomial-size gadget that is not constant. Lifting for dag-like
  protocols with a constant-size gadget would give constant-width families. Whether it holds is, as recalled, open
  (gadget sizes have been reduced but not to a constant; to be checked).
- **Frege.** Frege lines are arbitrary formulas with no cheap-protocol property across a split. Interpolation fails
  under cryptographic assumptions (Krajicek-Pudlak; Bonet-Pitassi-Raz; classical, in-project). No simplification found.
- **Scope.** Lifting is a statement about one proof system (cutting planes, and systems with cheap-protocol lines). It
  says nothing about NP vs coNP as such, which needs every proof system.

### (c+) Tools that click, the tying theorem, the shared property

**Existing tools that click here:**

| tool | what it supplies | mark |
|---|---|---|
| Cook-Reckhow | a proof system is a polynomial-time checker; the question is per system | classical |
| Ben-Sasson-Wigderson size-width | width lower bounds give size lower bounds for resolution | classical; Lean side (`size_width_exp`) |
| feasible interpolation (Krajicek 1998, Pudlak 1997) | cutting-planes lines are cheap real-communication protocols across a split | classical, in-project (`CP-DUALITY.md`) |
| lifting (Garg-Goos-Kamath-Sokolov 2018; gadget-size improvements since) | resolution width of `F` gives cutting-planes size of `F o g` | external, recalled |
| Hrubes-Pudlak, Fleming-Pankratov-Pitassi-Robere, Sokolov | cutting-planes lower bounds for random `Theta(log n)`-CNF | external, in-project |
| width lower bounds (Tseitin on expanders, random 3-CNF, pigeonhole) | the one-boundary cost | classical |

**Tying theorem and shared property.**
- The lifting theorem ties the form layer's `np_instance` (Lean) to the content.
- The shared property is **low communication across a two-party split**:
  - every cutting-planes line has it (interpolation);
  - a lifted search problem forbids it in proportion to the width (lifting).
- The resolution side meets the ledger through width, which the encoder already explains (a clause of width `w` keeps
  at most `1 - w/2n`).

**What the best existing content covers, and the audit it needs:**
- **Covered:** the crossing cost for cutting planes on every lifted formula `F o g` with `F` width-hard.
  - Audit: read GGKS (Theory of Computing 2020) for the exact gadget size, the proof-system model (dag-like, real
    communication, unbounded coefficients), and the exact size bound.
  - Read the later gadget-size improvements (recalled: Lovett-Meka-Mertz-Pitassi-Zhang, "lifting with sunflowers") to
    see how small a gadget is known to work.
- **Not covered:** unlifted constant-width formulas and Frege. No existing content solution is known; for Frege the
  cryptographic barrier to interpolation stands.

### (d) A first construction step for the next round

- **Lean (vacuity check of the NP instance).** State the lifting theorem as a named external hypothesis `LiftCP`:
  resolution width `w` of `F` implies the cutting-planes crossing cost of `F o g`, with `theta b` of order
  `w log n`. Instantiate `CrossingCost` and `np_instance` (`Unified/ProofSize.lean`) for lifted formulas. This shows the
  NP column of the ledger is inhabited by a class where the step is a theorem, and fixes the exact interface a
  constant-width version would have to meet.
- **CPU (cheap, connects to `refutation_needs_pair`).** For tiny formulas (pigeonhole 3 into 2, Tseitin on `K_4`) with
  a 2-bit XOR gadget, check by brute force two facts:
  - the all-1/2 fractional point of `F` lifts to a fractional point of `F o XOR`, so `refutation_needs_pair` applies to
    the lifted formula;
  - each party's half alone leaves every variable uniformly distributed (the lossless one-boundary encoder).

---

## 4. Is there one shared simplification?

The readings suggest two candidates: the **two-box handshake** and the **integrality of the quantum**.

**The handshake: a shared starting point, not a shared simplification.** In each problem every known partial result is
a two-copy construction:

| | the two copies | the shared root | known theorem using it | does it reach the open step? |
|---|---|---|---|---|
| Yang-Mills | two neighbouring boxes; or the box and its mirror | the face's flux label; the reflection plane | hyperbolic series (2D control, numerical); chessboard and Tomboulis-Yaffe (recalled) | **no**: the side and the uniform join loss remain |
| GRH | `f` and `f~`; `pi` and `pi~`; `C` and `C` | the mirror; the Frobenius graph | Weil over `F_q` (theorem); Rankin-Selberg zero-free regions | **no** over Z: the self-product is the missing object |
| NP vs coNP | two lines; two parties of a gadget | the rounded combination; the gadget's value | lifting (theorem, recalled) | **for lifted formulas only**; not constant width, not Frege |

The three theorems are different mathematics:
- for Yang-Mills and GRH, a positivity across a mirror (Cauchy-Schwarz, Hodge index);
- for NP, communication across a split.

`GRH-LENS.md` 9.4 already found the same split in kind: a bound on a sum against a bound on a minimum. So the handshake
does not give one simplification. It gives one *diagnosis*: in each problem the step must be paid at a shared root,
never by one side alone. That much is Lean in all three:
- Yang-Mills: the 0.881 bound is a statement about two pictures, and the two-box defect is a determinant;
- GRH: a one-sided assembly fails (`GRH/Transfer.lean`);
- NP: one line is lossless, and `refutation_needs_pair` holds.

**Integrality: the shared location of the cost, not a simplification.**
- **Yang-Mills:** it points the wrong way (`GRH-LENS.md` 9.2). An action floor makes twists rare, and O1 needs them
  nearly free.
- **GRH:** it works only with a tick (Stepanov over `F_q`). Over Z there is none.
- **NP:** the rounding *is* integrality. The quantum is the step itself, so integrality locates the cost exactly but
  does not price it.

**The pattern** [reading, with exact instances]. The handshake becomes a simplification exactly where the tick is
discrete and the pair is finite:

| where it simplifies | the discrete tick and finite pair | where the open step sits | what is missing |
|---|---|---|---|
| 2D gauge theory: independent plaquettes, join loss 0.13 (numerical) | each plaquette is one tick; no outside | 4D Yang-Mills | the outside is unbounded and the coupling runs |
| function fields: Weil's theorem | Frobenius, `2g` atoms | arithmetic over Z | no tick; infinitely many atoms |
| lifted formulas: GGKS | a finite gadget per variable | constant width; Frege | the gadget is not constant; Frege lines are unbounded |

In DMP language: the handshake certifies existence where both nodes are finite and the tick is fixed; the three open
steps are the three ways that can fail. **Verdict: the shared simplification does not hold.** What holds is a shared
starting point (the two-copy construction) and a shared diagnosis (the missing finite tick or finite pair). That
diagnosis is a candidate for the paper's framing, not progress on any step.

**The tying theorems under the construction principle** (PREP, last entry: clicking tools, top theorems through shared
properties, content left to the best content solutions):

| step | tying theorem | shared property of the tools | best existing content covers |
|---|---|---|---|
| O1 | ledger rate + Birkhoff-Hopf | one hyperbolic (Hilbert projective) distance = the encoder cost | Tomboulis-Yaffe: twist free energy implies area law; not the input number |
| GRH sign | Weil's criterion + Verblunsky | positive-definiteness of one Toeplitz form | zeta and Dirichlet completely (external, via the easy direction of Weil's criterion); nothing beyond |
| crossing cost | `np_instance` + lifting | low communication across a two-party split | cutting planes on lifted formulas; not constant width, not Frege |

The first two tying theorems share one property: the unit disk with its hyperbolic geometry, the encoder on the sphere
of `GRH-LENS.md` 6. That is the form layer's own top theorem, and it ties Yang-Mills and GRH at the level of tools. The
third uses a different property (communication), consistent with the split in kind found above. So under the
construction principle the honest framing is:
- one form-layer structure (the ledger and the encoder);
- two tool families (positivity in the disk; communication across a split);
- three content gaps, each named with its audit list.

**DMP spec cross-reading** [reading]. The spec's trust layer has the same shape:
- "proven" is an act with two independent witnesses (C22);
- a shared cause turns two witnesses into one (T29);
- a pressed instance is a one-witness system that is never axiomatically sound (T-P).

The mathematical counterpart of T29 is the two-box defect: two boxes that share a cause (a common outside) are not
independent witnesses, and the determinant `4 (p00 p11 - p01 p10)/S^2` (`twoBox_defect`, Lean) measures exactly that.
This is a vocabulary match only; it supplies no bound.

---

## 5. Status table

| item | status |
|---|---|
| O1, the GRH sign beyond Dirichlet, the crossing cost | **open** |
| O1 split into (side) and (join loss < 0.244) for three hand-over boxes | Lean for the arithmetic (existing); the split as a route **reading**; both parts **open** |
| 2D SU(2): join loss 0.08 to 0.19 < 0.244, three hand-over boxes clear O1, loss = the higher-sector tail | **classical** formulas, **numerical** |
| chessboard / mirror tiling removes the outsides, at the price of a global free energy | in-project (attempts), **recalled** literature |
| function-field instance: `abs(k_m) < 1` for `m < 2g`, `abs(k_2g) = 1`, from point counts | **classical** (Weil), **numerical** (four genus-2 curves) |
| fake off-circle quartet: `abs(k_4) = 1.21` | **numerical** |
| first rung of GRH (support up to (1/2) log 2) | **classical** (recalled), in-project |
| Rankin-Selberg zero-free regions, slack `1/log t` | **recalled** |
| the self-product of Spec Z with a Hodge index | **open** (known programme) |
| lifting (GGKS 2018): resolution width of `F` gives the CP size of `F o g` | **recalled**, external theorem |
| constant-size-gadget dag-like lifting | **recalled as open**, to be checked |
| one shared simplification | **fails**; shared starting point and diagnosis **reading** |

## 6. Files

- `docs/unified/OPEN-STEPS-DMP.md`: this note.
- `docs/unified/open_steps_check.py`, `open_steps_check.log`: part A (2D SU(2) series ledger), part B (genus-2 curves,
  Szego from point counts, off-circle control). Python with numpy and scipy, seconds.

## 7. Literature (recalled, not re-read in this round)

- A. Weil, Sur les courbes algebriques et les varietes qui s'en deduisent (1948); the Castelnuovo-Severi inequality.
- S. A. Stepanov (1969); E. Bombieri, Counting points on curves over finite fields (Seminaire Bourbaki, 1973).
- H. Yoshida, On Hermitian forms attached to zeta functions (1992); A. Connes, C. Consani, Weil positivity and trace
  formula, the archimedean place (2021).
- C. Deninger, on a cohomological interpretation of the explicit formula; A. Connes, C. Consani, the arithmetic site.
- Rankin-Selberg zero-free regions: C. J. Moreno (1985); J. Hoffstein, D. Ramakrishnan (1995).
- J. Froehlich, R. Israel, E. Lieb, B. Simon, CMP 62 (1978); E. Tomboulis, L. Yaffe, CMP 100 (1985).
- A. Garg, M. Goos, P. Kamath, D. Sokolov, Monotone circuit lower bounds from resolution, STOC 2018 (Theory of
  Computing 2020).
- J. Krajicek, Interpolation by a game (1998); P. Pudlak, JSL 1997.
