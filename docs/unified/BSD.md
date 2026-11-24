# Birch and Swinnerton-Dyer: the points on an existence line

Status: 2026-11-24. Answers the coordinator's direction "put the Birch-Swinnerton-Dyer conjecture into the project as an
instance of the DMP API, the points on an existence line", so that every Millennium-type problem is covered by the
framework. Earlier BSD was mention-only (`docs/mass-gap/weak-coupling/PREP.md`, entries "primes on a curve" and "scope
decision: Poincare as validation ... the other links only mentioned"). Builds on `API.md` (the template), `NAVIER-STOKES.md`
section 5 (the latest instance), `GRH-TIE-IN.md` (external inputs; the function-field instance) and `CONTOUR-SHIFT.md`
(Mathlib-only core modules).

Files:
- Lean, the Mathlib-only core: `ProofPhase/Unified/BSDCore.lean` (namespace `ProofPhase.BSD`, imports only Mathlib
  v4.34.0, 28 declarations).
- Lean, the API instance: `ProofPhase/Unified/BSDAPI.lean` (namespace `ProofPhase.API.BSD`, imports `ProofPhase.API` and
  the core, 46 declarations).
- `bsd-axioms.sh`, `bsd-axioms.log`: both modules build with no warnings; of the 74 declarations, 71 depend on the three
  standard axioms (`propext`, `Classical.choice`, `Quot.sound`), 2 on fewer, 1 on none; no `sorry`, no `admit`, no
  `native_decide`, no `axiom`. The log lists the core's imports (Mathlib only) and every `External` and `OpenStep` slot.
- Third-layer check: `bsd_check.py`, `bsd_check.log` (CPU, about 30 seconds; needs `mpmath`).

Status marks as in `NAVIER-STOKES.md`: **[Lean]** (proved here, standard axioms), **[Mathlib]** (proved in Mathlib
v4.34.0), **[classical]** (standard mathematics, recalled, not re-proved), **[external]** (a published result, recorded,
not checked here), **[numerical]** (computed here, `bsd_check.log`; refutes or guides, never establishes), **[reading]**
(an identification with DMP vocabulary, not a theorem), **[open]** (not proved by anyone). "Recalled" means from memory of
the literature, not re-checked in this round.

---

## 0. In plain words

**The problem.** An elliptic curve over the rationals, `y^2 = x^3 + a x + b`, has a group of rational points `E(Q)`. It is
finitely generated: finitely many points of finite order, plus `r` independent points of infinite order; `r` is the
rank [classical, Mordell 1922]. Separately, counting the points mod each prime `p` gives a number `a_p = p + 1 - #E(F_p)`,
and these numbers build an L-function `L(E, s)`. The Birch and Swinnerton-Dyer conjecture says: **the order of the zero of
`L(E, s)` at `s = 1` equals the rank** [open]. That is the owner's "the zeros follow existence": the zero counts the
independent rational points.

**What is known.** The L-function continues to the whole plane and has a functional equation (modularity, Wiles and
others) [external]. If the zero has order 0 or 1, the conjecture holds (Gross-Zagier, Kolyvagin) [external]. The parity
of the order is the root number, a sign `w = +-1` [classical; Lean here from the functional equation]. A positive
proportion of all curves satisfies it [external]. Open: everything from order 2 upwards, and the finiteness of the
Tate-Shafarevich group in general.

**What the API gives.** Filled into the template, BSD has the uniform shape:
- **Input:** a curve, its L-function made entire by modularity, its root number. External inputs: modularity
  (continuation and functional equation) and weak Mordell-Weil.
- **Proved structure** [Lean]: `E(Q)` is finitely generated (from weak Mordell-Weil, through Mathlib's height and descent
  theorems); its torsion is finite (Mathlib); the order of the zero does not depend on how `L` is continued; its parity is
  the root number; and the prime-by-prime ledger below.
- **One named open step:** BSD itself, "rank = order of the zero".
- **Conclusion** [Lean, given the open step]: **the existence line**: `E(Q)` is infinite exactly when `L(E, 1) = 0`, and
  `(-1)^rank = w`.

**The ledger.** The steps are the primes. At each prime the step factor is `N_p / p`, the number of points mod `p` over
`p` (the inverse local Euler factor at `s = 1`).
- **Hasse's bound `|a_p| <= 2 sqrt p` is the curve's own, proved, Riemann hypothesis**, and in the API it is exactly an
  encoder: the Frobenius eigenvalue `alpha` (with `alpha + conj alpha = a_p`, `alpha conj alpha = p`) is a rotated image of
  `sqrt p` with the same norm. The encoder's reflection coefficient is `cos theta_p = a_p / (2 sqrt p)`, its Szego factor is
  `sin^2 theta_p` (the Sato-Tate density), and the point count is `N_p = |1 - alpha|^2` [Lean; Hasse itself is an
  external input].
- The encoder bounds put every step factor between `(1 - p^{-1/2})^2` and `(1 + p^{-1/2})^2`. So **no finite stage of the
  Euler product vanishes**: the zero at `s = 1` is a property of the whole chain, a rate, never of a step [Lean].
- The 1965 form of the conjecture is literally a ledger balance: `prod_{p <= x} N_p / p ~ C (log x)^r`, so the rank is the
  growth rate of the ledger. By Goldfeld's theorem this form implies BSD (and the Riemann hypothesis for `L(E, s)`)
  [external]. It is a second card with that balance as its open step [Lean for the plumbing].

**The slot is not empty.** For `y^2 = x^3 - x` (conductor 32), with its known values as external inputs (`E(Q)` has the
four points `O, (0, 0), (1, 0), (-1, 0)`, by Fermat's descent; `L(E, 1) = 0.6555... != 0`), the card's open step holds and
its conclusion follows, including the root number `+1` [Lean from the external inputs]. The point counts mod `p` run in
Lean and are proved equal to Mathlib's count. Hasse's check runs at every odd prime below 100, and at `p = 5` it is checked by
the kernel [Lean]. Numerically, both example curves (also `y^2 + y = x^3 - x`, rank 1) satisfy Hasse at every prime
below 20000, and their L-values match the refined formula to 10 digits [numerical].

**The owner's reading, exactly (section 4).** "The zeros follow existence" has an exact counterpart: the order of the zero
at `s = 1` equals the number of independent rational points. Its first level, "a zero exists exactly when a point of
infinite order exists", is the existence line. One direction of it is **proved**: a point of infinite order forces
`L(E, 1) = 0` (Kolyvagin, with modularity; the contrapositive of "`L(E, 1) != 0` gives finitely many points"). The other
direction, "a zero forces a point", is proved only when the zero is simple: the Heegner point constructs the point. The care
point: the classical proofs do not run the way the reading pictures it. Existence does not produce the zero by counting.
The zero of order one *produces* the point (Heegner), and a nonzero value *forbids* points (Kolyvagin). From order 2
upwards nothing is known in either direction. Nothing here advances BSD.

---

## 1. The statement and the state of the art

### 1.1 The Clay statement [classical]

Let `E` be an elliptic curve over `Q`. Its points `E(Q)` form a finitely generated abelian group (Mordell 1922), so
`E(Q) = Z^r + T` with `T` finite; `r` is the rank. For each prime `p` of good reduction let `a_p = p + 1 - #E(F_p)`. The
L-function is the Euler product

    L(E, s) = prod_{p bad} L_p(p^{-s})^{-1} * prod_{p good} (1 - a_p p^{-s} + p^{1 - 2s})^{-1},

which converges for `Re s > 3/2`. The Clay problem (Wiles' official description) asks to prove: **the Taylor expansion of
`L(E, s)` at `s = 1` has the form `c (s - 1)^r + higher terms` with `c != 0` and `r` the rank of `E(Q)`**. In particular
`L(E, 1) = 0` exactly when `E(Q)` is infinite. The description also states the refined conjecture:

    c = L^{(r)}(E, 1) / r! = Omega_E * Reg_E * #Sha(E) * prod_p c_p / #T^2,

with `Omega_E` the real period, `Reg_E` the regulator (the determinant of the canonical height pairing on a basis of the
free part), `Sha(E)` the Tate-Shafarevich group (conjectured finite), `c_p` the Tamagawa numbers. For the rank part to make
sense, `L(E, s)` must be defined near `s = 1`, which needs the analytic continuation (1.2).

### 1.2 What is proved

| result | statement | mark |
|---|---|---|
| Mordell 1922, Weil 1929 | `E(Q)` (and `E(K)` for a number field `K`) is finitely generated; the proof is weak Mordell-Weil (`E(Q)/2E(Q)` finite) plus descent with the height | [classical] |
| Hasse 1933-36, Weil 1948 | `|a_p| <= 2 sqrt p` (the Riemann hypothesis for the curve mod `p`) | [classical] |
| Deuring 1953-56 | for curves with complex multiplication, `L(E, s)` is a Hecke L-function: entire, with a functional equation | [classical] |
| Wiles 1995, Taylor-Wiles 1995, Breuil-Conrad-Diamond-Taylor 2001 | every `E/Q` is modular; hence `L(E, s)` continues to an entire function and the completed `xi(s) = N^{s/2} (2 pi)^{-s} Gamma(s) L(E, s)` satisfies `xi(2 - s) = w xi(s)`, `w = +-1` (Hecke) | [external] |
| Coates-Wiles 1977 | CM curves: `L(E, 1) != 0` implies `E(Q)` finite | [external] |
| Gross-Zagier 1986 | `L'(E, 1)` is a nonzero multiple of the canonical height of a Heegner point; so a simple zero gives a point of infinite order | [external] |
| Kolyvagin 1988-90 (Euler systems), with modularity and the nonvanishing of auxiliary twists (Bump-Friedberg-Hoffstein, Murty-Murty, 1990) | analytic rank 0 or 1 implies rank = analytic rank and `Sha` finite | [external] |
| Rubin 1987 | CM curves with `L(E, 1) != 0`: `Sha` finite | [external] |
| Buhler-Gross-Zagier 1985 | the curve 5077a has a zero of order exactly 3 and rank 3: BSD (rank part) holds for this one curve of order 3 | [external, recalled] |
| Kato 2004, Skinner-Urban 2014, and later work | for many curves of analytic rank 0 or 1, the `p`-part of the leading-coefficient formula, for many primes `p` | [external, recalled] |
| parity | the order's parity is the root number (functional equation; Lean here, `analytic_parity`); Monsky 1996 (2-Selmer parity), Nekovar, Dokchitser-Dokchitser 2010 (the `p`-parity conjecture for `E/Q`: `(-1)^{Selmer rank} = w` for every `p`); so finiteness of `Sha` would give `(-1)^rank = w` | [external] |
| Bhargava-Shankar 2015, with Skinner-Urban, Zhang, Bhargava-Skinner-Zhang 2014 | the average rank (curves ordered by height) is below 1; a positive proportion of curves have rank 0, a positive proportion rank 1, and BSD (rank part) holds for a positive proportion (at least about 66 percent) of all curves | [external, recalled; context, not used] |

### 1.3 What is open [open]

- The rank part for analytic rank at least 2 in general: no construction of two or more independent points from a
  higher-order zero (no "higher Heegner points"), and no bound "rank <= order" beyond order 1.
- No curve is known for which an analytic rank of 4 or more is proved: a vanishing can be certified only up to order 3
  (a value by modular symbols, a first derivative by Gross-Zagier, each with parity), and numerics cannot certify a zero
  [recalled].
- Finiteness of `Sha` in general (known for analytic rank <= 1).
- The full refined formula for all curves of analytic rank 0 and 1 (all primes `p` at once), and any case of rank >= 2
  beyond individual checks.
- The Riemann hypothesis for `L(E, s)` (zeros on `Re s = 1`): part of GRH beyond Dirichlet L-functions.
- Boundedness of ranks (curves of rank at least 28 are known, Elkies 2006; at least 29, Elkies-Klagsbrun 2024
  [recalled]).

---

## 2. What Mathlib v4.34.0 has, and what it lacks

Read in `Mathlib/AlgebraicGeometry/EllipticCurve/` (19 files, about 9800 lines), `Mathlib/NumberTheory/Height/` and
`Mathlib/GroupTheory/Descent.lean`.

**Defined and proved [Mathlib]:**

| item | where | content |
|---|---|---|
| the curve | `Weierstrass.lean` | `WeierstrassCurve R` (coefficients `a1 a2 a3 a4 a6`), `b`- and `c`-invariants, discriminant `Δ`, `j`; `IsElliptic` = `Δ` a unit; base change `map` |
| changes of variables, normal forms, models with given `j` | `VariableChange.lean`, `NormalForms.lean`, `ModelsWithJ.lean`, `IsomOfJ.lean` | isomorphism classes over algebraically closed fields by `j` |
| the group of points | `Affine/Point.lean` (also `Jacobian/`, `Projective/`) | `W.toAffine.Point` (nonsingular affine points with the point at infinity), the chord-tangent law, and an `AddCommGroup` instance (associativity through the class group of the coordinate ring); `pointEquiv` to the solutions of the equation |
| division polynomials | `DivisionPolynomial/` | `ψ_n`, `φ_n`, degrees and leading coefficients |
| reduction | `Reduction.lean` | integral and minimal models over the fraction field of a DVR, `reduction`, good, multiplicative (split or not) and additive reduction |
| the L-function, as a formal object | `LFunction.lean` (2026) | the local polynomial (`1 - a T + q T^2` at good reduction with `a = q + 1 - #W(κ)`, `1 -+ T` multiplicative, `1` additive), the local Euler factor, `WeierstrassCurve.LFunction` (the Euler product as an arithmetic function, over any number field) and `WeierstrassCurve.LSeries` (its Dirichlet series as a function of `s`) |
| heights | `NumberTheory/Height/EllipticCurve.lean` | the naive height `Point.naiveHeight`, the approximate parallelogram law `approx_parallelogram_law`, Northcott's property over number fields, **finite torsion** `finite_torsion` |
| descent | `GroupTheory/Descent.lean` | `AddCommGroup.fg_of_descent'`: `G/2G` finite + a height with the parallelogram law and Northcott gives `G` finitely generated ("one of the main ingredients of the standard proof of the Mordell-Weil theorem") |

**Missing (Mathlib gaps):**
- **weak Mordell-Weil** (`E(Q)/2E(Q)` finite; needs Kummer theory, finiteness of class groups and unit groups for the
  2-division field), hence **Mordell-Weil** itself;
- **the rank** as a named object (here: `Module.finrank ℤ E(Q)`, the true rank once `E(Q)` is finitely generated);
- **Hasse's bound** (no theory of the number of points over a finite field beyond finiteness), hence the convergence of
  the L-series for `Re s > 3/2`;
- **analytic continuation, functional equation, conductor, root number** (all through modularity; also the CM case);
- the **canonical (Neron-Tate) height**, the **regulator**, the **real period**, **Sha**, **Selmer groups**, **Tamagawa
  numbers**, **Heegner points**;
- the link from `LFunction`'s local factor at the completion `Q_p` (residue field of `Z_p`) to a count over `ZMod p`
  (the identification is routine but not stated; not done here either).

**What this round built to fill the core's needs** (IM rule: Mathlib-only modules, `BSDCore.lean`):
- Mordell-Weil from weak Mordell-Weil (`mordellWeil_of_weak`), from Mathlib's height and descent [Lean];
- the rank, and "rank 0 iff `E(Q)` finite", "points of infinite order iff rank > 0" [Lean];
- the continuation as a named property (`IsContinuation`), its uniqueness and the well-definedness of the order [Lean];
- the gamma factor, analytic and nonzero at `s = 1`, and the parity theorem from the functional equation [Lean];
- the BSD statement, the refined statement on named quantities, the existence line [Lean];
- a point count over `ZMod p` that runs, proved equal to Mathlib's `Nat.card` of the reduced curve at good primes, and a
  decidable Hasse check proved equal to the real inequality [Lean].

---

## 3. BSD through the DMP API (`BSDAPI.lean`)

### 3.1 The template, filled in

| API concept | BSD | in Lean |
|---|---|---|
| well-defined input | a curve `W` over `Q` (elliptic), its conductor `N`, an entire `Λ` and a sign `w`; external: `Λ` continues `L(E, s)`, the completed function has the functional equation with root number `w`, `E(Q)/2E(Q)` is finite | `Input` |
| encoder | at each prime: state `sqrt p`, rotated image the Frobenius eigenvalue `alpha`; the shared root `‖alpha‖ = sqrt p` **is** Hasse's bound; reflection coefficient `cos theta_p = a_p/(2 sqrt p)`, Szego factor `sin^2 theta_p` in `[0, 1]` | `frob`, `frob_refl`, `frob_szego`, `count_normSq` |
| margin (`Margin`) | the partial Euler product `P_n = prod_{i < n} N_{p_i}/p_i`, keeping at least `(1 - p^{-1/2})^2` per prime | `EulerData.lower` |
| chain (`Chain 0`) | the same product, with cost `-log (1 + p^{-1/2})^2` per prime, floor 0 | `EulerData.upper`, `P_le` |
| open-step slot | BSD: rank = order of the zero at `s = 1`; in ledger form: `P_n ~ C (log p_n)^rank` | `problem`, `ledgerCard` |
| external-input slot | modularity (continuation, functional equation), weak Mordell-Weil, Hasse, Gross-Zagier-Kolyvagin, Goldfeld; for the example: Deuring, `L(E, 1) != 0`, Fermat's descent | `Input.cont`, `.fe`, `.weak`, `EulerData.hasse`, `LowRank`, `LedgerInput.goldfeld`, `Data32` |
| computable layer | point counts mod `p`, `a_p`, the Hasse check, each proved right | `countZ`, `apZ`, `hasseZ`, `count_correct`, `hasseZ_iff`, `count_E32` |
| problem cards | the existence line; the 1965 ledger form | `problem`, `ledgerCard` |

### 3.2 What is proved, and from what

**Without the open step** (`unconditional`) [Lean from the external inputs]:
- `E(Q)` is finitely generated (`mordellWeil_of_weak`, from `weak`; Mathlib's descent and height);
- its torsion is finite (Mathlib, unconditional);
- every continuation has the same order at `s = 1` (`order_welldefined`, the identity theorem);
- if that order is `n`, then `w = (-1)^n` (`analytic_parity`, from `fe`; the gamma factor is analytic and nonzero at 1,
  `completed_order`).

**The card** (`problem`) [Lean]: open step `BSDStatement W Λ` (`(rank : ℕ∞) = analyticOrderAt Λ 1`); conclusion:
- `Infinite E(Q) <-> Λ 1 = 0` (`existence_line`): through `rank > 0 <-> E(Q)` infinite (finite generation plus finite
  torsion) and `order != 0 <-> Λ 1 = 0`;
- `w = (-1)^rank` (`rank_parity`).

**The low-rank theorem in its slot** (`LowRank`, `open_of_lowRank`): Gross-Zagier-Kolyvagin as an `External` fills the
card's open step whenever the order is at most 1 [Lean for the plumbing; external for the content].

**The ledger** [Lean; Hasse as the external input]:
- `factor_bounds`: `(1 - q^{-1/2})^2 <= (q + 1 - a)/q <= (1 + q^{-1/2})^2` from `a^2 <= 4 q`;
- `no_finite_zero`: `P_n > 0` for every `n` (the API's `Margin.pos`);
- `P_le`: `P_n <= prod (1 + p^{-1/2})^2` (the API's `Chain.ledger`).

**The ledger card** (`ledgerCard`): open step `EulerData.Balance (rank)`, the 1965 form; conclusion BSD; proof:
Goldfeld's theorem in an `External` slot [Lean for the plumbing; external for the content]. The `External` is true only
when the prime data `D` are the curve's own; the input structure documents this, and the Lean does not check it (that would
need the Mathlib gap of section 2, local factor versus `ZMod p` count, at every prime).

### 3.3 The example: `y^2 = x^3 - x`

| item | status |
|---|---|
| `E32`: the curve over `Q`, `Δ = 64`, elliptic (`E32_Δ`, instance) | [Lean] |
| `(0, 0)`, `(1, 0)`, `(-1, 0)` are on it (`E32_points`) | [Lean] |
| `count_E32`: the computed count mod `p` is Mathlib's `Nat.card` of the reduced curve, every odd prime | [Lean] |
| `a_p` for `p = 3, ..., 37`: `0, -2, 0, 0, 6, 2, 0, 0, -10, 0, -2` (`#eval`; zero at `p = 3 mod 4`: complex multiplication by `i`) | [Lean, runs] |
| Hasse check at every odd prime below 100 (`#guard`); at `p = 5` by the kernel (`hasse_E32_five`) | [Lean] |
| `Data32`: continuation and functional equation (Deuring; conductor 32), `L(E, 1) != 0`, `E(Q)` finite (Fermat: 1 is not a congruent number) | [external] |
| `bsd_E32`: BSD holds (rank 0 = order 0); `card_E32`: the card's open step is filled, its conclusion holds, and the root number is `+1` | [Lean from the external inputs] |

Numerically (`bsd_check.log`) [numerical]:
- 32a2 (`y^2 = x^3 - x`): Hasse holds at all 2262 primes below 20000 (largest `|a_p|/(2 sqrt p)` = 0.99989).
  `L(E, 1) = 0.655514388573`. The real period over both components is `Omega = 5.2441151066`, and `L(E, 1)/Omega = 0.1250000000`.
  This equals the refined right-hand side `c_2 Sha / T^2 = 2 * 1 / 16` with the recalled `c_2 = 2`, `Sha = 1`, `T = 4`.
- 37a1 (`y^2 + y = x^3 - x`, root number `-1`): Hasse holds at the same primes. `L'(E, 1) = 0.305999773834`.
  `(0, 0)` is a point and `5P = (1/4, -5/8)` is not integral, so `P` has infinite order (Nagell-Lutz).
  `L'(E, 1)/Omega = 0.0511114083`, which matches the recalled regulator `0.0511114082` (with `c_37 = Sha = T = 1`).
- The Euler ledger: `prod_{p <= x} N_p/p / (log x)^r` at `x = 100, 1000, 5000, 20000` is
  - 32a2: `1.65, 2.24, 2.12, 2.25`, against `sqrt 2 / L(E, 1) = 2.157`;
  - 37a1: `6.82, 6.79, 7.96, 7.19`, against `sqrt 2 e^gamma / L'(E, 1) = 8.23`.

  The products oscillate and converge slowly, as expected at the centre of the critical strip. The `sqrt 2` is the
  recalled constant of Goldfeld 1982 (explained by K. Conrad 2005); the rank-0 numbers support it, and without the
  `sqrt 2` the target would be 1.53.

---

## 4. What would close it, and what DMP says

**The owner's reading:** "the zeros follow existence": the order of the zero of `L(E, s)` at `s = 1` counts the rational
points.

**The exact mathematical counterpart.** Three levels, from weakest to strongest:
1. **The existence line** (`existence_line`): `L(E, 1) = 0` exactly when `E(Q)` has a point of infinite order.
   - "Existence forces the zero" (a point of infinite order gives `L(E, 1) = 0`) is **proved** for every `E/Q`
     [external]. It is the contrapositive of Kolyvagin's theorem, with modularity: `L(E, 1) != 0` gives rank 0.
   - "The zero forces existence" is **proved when the zero is simple** (Gross-Zagier: the Heegner point has nonzero
     height) and **open** when the order is 2 or more. With root number `-1`, finiteness of `Sha` would settle it by parity
     (Dokchitser-Dokchitser), but that finiteness is itself open.
2. **The rank part**: order = rank. Proved for order 0 and 1 [external], open from 2 on [open].
3. **The ledger form** (1965): `prod_{p <= x} N_p/p ~ C (log x)^rank`. Here the rank is the growth rate of the local
   counts, which is the reading taken literally: the global points show up as a slight excess of points mod `p`, and that
   excess, summed over primes, grows like `rank * log log x` (the heuristic behind the 1965 form, recalled). Goldfeld: this form implies level 2 and the Riemann
   hypothesis for `L(E, s)` [external]. It is strictly stronger than BSD and is open [open].

**The care points.**
- **Direction.** The proved results do not run "existence, therefore a zero, by counting". At order one the analytic side
  *constructs* the point: the derivative `L'(E, 1)` is the height of the Heegner point. A nonzero value *forbids* points
  (Kolyvagin's Euler system bounds the Selmer group). So the reading's arrow is proved at the first level only, and by a
  different mechanism than counting.
- **No finite stage sees the zero.** Every partial Euler product is positive (`no_finite_zero`), and each prime moves it by
  a factor within `(1 +- p^{-1/2})^2` (Hasse). The zero, and its order, are infinite-horizon properties: a rate. This is the
  same shape as O1 in the other instances: the open step is about the whole chain, never about one step. Conversely, a
  zero at `s = 1` is not visible in any finite set of `a_p`: the order is decided by all primes together.
- **Two RHs, one proved.** Hasse's bound is the curve's local Riemann hypothesis, proved and an encoder. The Riemann
  hypothesis for `L(E, s)` (global) is open, part of GRH beyond Dirichlet; the ledger form of BSD would imply it.
  BSD itself does not need it, but every route from the ledger form to BSD passes through it (Goldfeld). This is the same
  split as in `GRH-TIE-IN.md`: the function-field instance (genus `g` over `F_q`, Weil's theorem) is proved, the
  number-field one is open. For `g = 1` the function-field instance's `WeilBound` is exactly Hasse's bound for `E mod p`.
- **Parity is free; the size is not.** The functional equation (the mirror `s <-> 2 - s`) fixes the parity of the order
  (`analytic_parity`, [Lean]). The order itself, which is the content, is not fixed by any symmetry.

**What would close it.** A construction of `r` independent rational points from a zero of order `r` (a higher analogue of
Heegner points; candidates: higher derivatives of p-adic L-functions, Darmon's Stark-Heegner points, all conjectural), plus
an upper bound `rank <= order` beyond order 1 (Euler systems of higher rank, or Iwasawa main conjectures together with
nondegeneracy of `p`-adic heights). In the API's terms: the card's open step for orders 2 and up. Nothing in this round
proves any part of it.

**What DMP adds** [reading]. BSD fits the template without strain: the input is well defined (modularity), the structure
around it is proved (Mordell-Weil from its weak form, parity, Hasse as an encoder, the ledger bounds), and the one open step
is a balance between two counts: existence (independent points) on one side, the zero (the vanishing rate of the Euler
ledger) on the other. In the triad of `PREP.md` (Yang-Mills existence, GRH non-existence, NP vs coNP their interaction),
BSD is an equation between an existence count and a zero count. That is the owner's "zeros follow existence", and it now
sits in a named slot of the framework, beside the others.

---

## 5. Status table

| item | statement | status |
|---|---|---|
| BSD, rank part | rank `E(Q)` = order of `L(E, s)` at `s = 1` | [open]; the card's `OpenStep` |
| BSD, refined | leading coefficient = `Omega Reg Sha prod c_p / T^2` | [open]; `RefinedBSD` (named quantities), `order_of_refined` [Lean] |
| Mordell-Weil | `E(Q)` finitely generated | [classical]; [Lean] from weak Mordell-Weil (`mordellWeil_of_weak`) |
| weak Mordell-Weil | `E(Q)/2E(Q)` finite | [classical]; `External`; Mathlib gap |
| torsion | finite | [Mathlib] (`finite_torsion`), re-exported `torsion_finite` |
| rank 0 iff finite; infinite iff rank > 0 | for finitely generated `E(Q)` | [Lean] |
| continuation, functional equation | entire `L(E, s)`, `xi(2 - s) = w xi(s)` | [external] (modularity; Deuring for CM); `External` |
| uniqueness of the continuation; well-defined order | | [Lean] |
| gamma factor | analytic, nonzero at 1; completed order = order | [Lean] |
| parity | `w = (-1)^{order}` | [Lean] from the functional equation |
| existence line | BSD gives `E(Q)` infinite iff `L(E, 1) = 0` | [Lean] given BSD; one direction [external] (Kolyvagin) |
| analytic rank <= 1 | BSD holds | [external] (Gross-Zagier, Kolyvagin); `LowRank` slot |
| Hasse | `|a_p| <= 2 sqrt p` | [classical]; `External`; Mathlib gap; checked by computation for `E32` at odd `p < 100` (`#guard`), by the kernel at `p = 5`; numerically for two curves at `p < 20000` |
| Hasse as an encoder | the shared root is Hasse; refl = `cos theta_p`; Szego = `sin^2 theta_p`; `N_p = |1 - alpha|^2` | [Lean] |
| Euler ledger | step factors within `(1 +- p^{-1/2})^2`; no finite stage vanishes | [Lean] given Hasse |
| 1965 form | `prod N_p/p ~ C (log x)^r` | [open]; `ledgerCard`; Goldfeld [external] |
| point counts | computed count = Mathlib's `Nat.card` at good primes | [Lean] |
| example `y^2 = x^3 - x` | BSD from its known values; root number `+1` | [Lean] from [external] inputs |
| example values | `L(E, 1)`, `L'(E, 1)` of 37a1, refined-formula ratios | [numerical] |
| average rank, positive proportions | Bhargava-Shankar and others | [external, recalled]; context only |
| owner's reading | "zeros follow existence" = the existence line and the rank equation; arrow proved at the first level only, by construction (Heegner) and exclusion (Kolyvagin) | [reading] |
| Clay problem | not advanced by this round | unchanged here |

---

## 6. Files

| file | content |
|---|---|
| `ProofPhase/Unified/BSDCore.lean` (namespace `ProofPhase.BSD`, imports `Mathlib` only) | `Pts`, `WeakMordellWeil`, `mordellWeil_of_weak`, `torsion_finite`, `algRank`, `algRank_eq_zero_iff`, `infinite_iff_algRank_pos`, `IsContinuation`, `continuation_unique`, `order_welldefined`, `zero_iff_order_ne_zero`, `order_parity`, `gammaFactor`, `gammaFactor_analyticAt`, `gammaFactor_one_ne_zero`, `completed_order`, `FunctionalEquation`, `analytic_parity`, `BSDStatement`, `existence_line`, `rank_parity`, `RefinedBSD`, `order_of_refined`, `countZ`, `apZ`, `hasseZ`, `hasseZ_iff`, `count_correct` |
| `ProofPhase/Unified/BSDAPI.lean` (namespace `ProofPhase.API.BSD`) | `frobAlpha`, `frobAlpha_normSq`, `norm_frobAlpha`, `count_normSq`, `frob`, `frob_refl`, `frob_szego`, `factor_bounds`, `EulerData` (with `p`, `p_gt_one`, `a`, `hasse'`, `fac`, `P`, `share`, `top`, `fac_bounds`, `share_pos`, `top_pos`, `fac_nonneg`, `P_nonneg`, `P_succ`, `lower`, `upper`, `no_finite_zero`, `P_le`, `Balance`), `Input`, `unconditional`, `problem`, `LowRank`, `open_of_lowRank`, `LedgerInput`, `ledgerCard`, `E32`, `E32_Δ`, `E32_points`, `E32Z`, `E32Z_Δ`, `count_E32`, `hasse_E32_five`, `Data32`, `input32`, `bsd_E32`, `card_E32` |
| `docs/unified/bsd-axioms.sh`, `bsd-axioms.log` | build of both modules, the core's imports, `#print axioms` for all 74 declarations, source grep, the list of `External` and `OpenStep` slots |
| `docs/unified/bsd_check.py`, `bsd_check.log` | point counts and Hasse for 32a2 and 37a1 at `p < 20000`, the Frobenius encoder, `L(E, 1)` and `L'(E, 1)`, the point `(0, 0)` on 37a1, the Euler ledger, the refined-formula ratios |

Imported, not edited: `ProofPhase/API.lean` (`Encoder`, `Margin`, `Chain`, `Problem`, `OpenStep`, `External`); from
Mathlib: `WeierstrassCurve`, `Affine.Point`, `Affine.pointEquiv`, `Affine.approx_parallelogram_law`, `Affine.finite_torsion`,
`AddCommGroup.fg_of_descent'`, `WeierstrassCurve.LSeries`, `analyticOrderAt`, `Complex.Gamma`.

Not done here, left to the coordinator: a BSD row in `API.md` section 4 and an import line in `Unified/All.lean` (this
round touched only its new files).

Sources: none fetched this round. The state of the art (section 1) is recalled from the literature: Wiles' Clay problem
description; Silverman, *The Arithmetic of Elliptic Curves*; Gross-Zagier 1986; Kolyvagin 1990; Goldfeld 1982;
K. Conrad 2005 (partial Euler products on the critical line); Bhargava-Shankar 2015; Dokchitser-Dokchitser 2010. Mathlib was
read directly (v4.34.0, in the build folder). The numbers in 3.3 are computed here; the Tamagawa number of 32a2 and the
regulator of 37a1 are recalled, and the computed ratios agree with them to 9 and 10 digits.
