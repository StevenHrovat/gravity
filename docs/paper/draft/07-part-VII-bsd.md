# Part VII. Birch and Swinnerton-Dyer: the card, three named parts, and the one open step

*Draft 2, 2026-11-24. Prose, with every result marked. Modules of the Mathlib-only core live in DMP.IM (the public `im` repository,
`arsenal/Arsenal/`) and are written `Arsenal.BSD...`; they are being merged into `im` now. Lean paths of this repository are relative to
`docs/mass-gap/formal/ProofPhase/`; notes are relative to `docs/unified/`. Claim labels (VII.n) are listed in
`../claims-incoming/VII-bsd.md` until the coordinator merges them into `../CLAIMS.md`.*

## VII.0 What is proved, by whom, and what this part does

**The Clay problem** (Wiles' official description) **[classical]**. Let E be an elliptic curve over the rationals. Its group of
rational points E(Q) is finitely generated (Mordell 1922), so it is a finite group of torsion points plus r independent points of
infinite order. The number r is the **rank**. For each prime p of good reduction let a_p = p + 1 - #E(F_p). The numbers a_p build the
L-function L(E, s) as an Euler product. The conjecture says: **the Taylor expansion of L(E, s) at s = 1 is c (s - 1)^r + higher terms,
with c not zero and r the rank.** In particular L(E, 1) = 0 exactly when E(Q) is infinite. Clay's text also gives the refined
formula for c: the real period, the regulator, the order of the Tate-Shafarevich group, the Tamagawa numbers and the torsion order
enter. The statement needs L(E, s) near s = 1, so it needs the analytic continuation, which is the modularity theorem (Wiles, Taylor-Wiles,
Breuil-Conrad-Diamond-Taylor) **[external]**.

**State of the problem (2026-11-24).** The rank statement is proved when the order of the zero is 0 or 1 (Gross-Zagier, Kolyvagin, with
modularity) **[external]**. It is **open** from order 2 on. The notes record no claimed proof of the general statement. **This part
proves no case of the conjecture that was not already known**, and its Lean contains no new theorem about elliptic curves that
experts did not have.

**What this part does.** It states BSD as a property of one Weierstrass equation and proves in Lean what Mathlib gives about it
(VII.3). It puts BSD on the DMP API as a card with one named open step (VII.2). It records what is borrowed and its exact status
(VII.4), states the one open step (VII.5), and attaches the owner's readings, short (VII.6). Three classical theorems that Mathlib
lacks are carried as **named parts**, not axioms: weak Mordell-Weil, Hasse's bound, and one Euler product bound. They are
theorems of others, not open problems. They are missing from the library, not from mathematics.

## VII.1 The problem as stated, and what is known

**VII.1.1 What is proved** (recalled from the literature; not re-read for this draft).

| Result | Statement | Mark |
|---|---|---|
| Mordell 1922, Weil 1929 | E(Q), and E(K) for a number field K, is finitely generated. The proof is weak Mordell-Weil (E(Q)/2E(Q) is finite) plus descent with a height | classical |
| Hasse 1933-36, Weil 1948 | `abs(a_p) <= 2 sqrt p`: the Riemann hypothesis of the curve over F_p | classical |
| Deuring 1953-56 | for curves with complex multiplication, L(E, s) is a Hecke L-function: entire, with a functional equation | classical |
| Wiles 1995, Taylor-Wiles 1995, Breuil-Conrad-Diamond-Taylor 2001 | every E/Q is modular, so L(E, s) is entire and the completed function has a functional equation with sign w = +1 or -1 | external |
| Coates-Wiles 1977; Rubin 1987 | CM curves: L(E, 1) not zero gives E(Q) finite (Coates-Wiles) and Sha finite (Rubin) | external |
| Gross-Zagier 1986 | L'(E, 1) is a nonzero multiple of the height of a Heegner point; a simple zero gives a point of infinite order | external |
| Kolyvagin 1988-90, with modularity | analytic rank 0 or 1 gives rank = analytic rank and Sha finite | external |
| Buhler-Gross-Zagier 1985 | the curve 5077a has a zero of order exactly 3 and rank 3 | external, recalled |
| Kato 2004; Skinner-Urban 2014; later work | for many curves of analytic rank 0 or 1, the p-part of the refined formula for many p | external, recalled |
| Monsky 1996; Nekovar; Dokchitser-Dokchitser 2010 | the p-parity conjecture for E/Q; so finiteness of Sha would give `(-1)^rank = w` | external |
| Bhargava-Shankar 2015, with Skinner-Urban and others | the average rank is below 1; a positive proportion of curves have rank 0 and a positive proportion rank 1; the rank part holds for a positive proportion of all curves | external, recalled; context only |

**VII.1.2 What is open** **[open]**.

* The rank part for analytic rank 2 or more, in general. There is no construction of two or more independent points from a higher
  zero (no higher Heegner points), and no bound "rank <= order" beyond order 1.
* The finiteness of Sha in general (known for analytic rank at most 1).
* The refined formula for all curves of analytic rank 0 and 1, at all primes at once, and any case of rank 2 or more beyond single
  curves.
* The Riemann hypothesis for L(E, s) (the zeros on the line `re s = 1`), part of GRH beyond Dirichlet L-functions (Part IV).
* No curve of proved analytic rank 4 or more is known. A zero can be certified only up to order 3 (a value by modular symbols, a
  first derivative by Gross-Zagier, each with parity). Numerics cannot certify a zero **[classical, recalled]**.

## VII.2 The card

The DMP API (`docs/unified/API.md`) gives every problem one shape: a well-defined input, a proved structure on it, one named open
step in a slot, and external inputs in their own slot. BSD has two layers. The Mathlib-only core is `Arsenal.BSD` in DMP.IM. The
instance of the API is `Unified/BSDAPI.lean` in this repository (namespace `ProofPhase.API.BSD`). The table fills the template.

| API concept | BSD | Lean |
|---|---|---|
| **Input** | an elliptic curve W over Q; a function `Lam` meant to be its continued L-function; a sign `w`. Over IM: any number field K | `Input` (`BSDAPI`); `Arsenal.BSD.Pts` |
| **Encoder** | at each prime p: state `sqrt p`, rotated image the Frobenius eigenvalue `alpha`. The shared root `norm alpha = sqrt p` is Hasse's bound. Reflection coefficient `a_p / (2 sqrt p)`, Szego factor `1 - a_p^2/(4p)` | `frob`, `frob_refl`, `frob_szego` |
| **Margin and chain** | the partial Euler product `P_n = product of N_p / p`. It keeps at least `(1 - p^{-1/2})^2` per prime and gains at most `(1 + p^{-1/2})^2` | `EulerData.lower`, `EulerData.upper` |
| **Open-step slot** | BSD: the L-series continues to `s = 1` and the order of its zero there is the rank. In ledger form: `P_n ~ C (log p_n)^rank` | `BSDStatement` (core); `problem`, `ledgerCard` |
| **External-input slot** | modularity (continuation, functional equation), weak Mordell-Weil, Hasse, Gross-Zagier-Kolyvagin, Goldfeld. In IM, weak Mordell-Weil, Hasse and the Euler product bound are named parts | `Input.cont`, `.fe`, `.weak`, `EulerData.hasse`, `LowRank`, `LedgerInput.goldfeld`; `R136a1` |
| **Computable layer** | point counts over any finite ring, `a_p`, the Hasse check, each proved right | `Arsenal.BSD.count`, `frobTrace`, `hasseCheck`, `count_correct`, `hasseCheck_iff` |

The cards, in the card shape:

| Card | Input | The one open step | Conclusion | External input |
|---|---|---|---|---|
| **BSD** (`problem`) | a curve W over Q, a function `Lam`, a sign `w` | `BSDStatement W`: rank equals the order of the zero at s = 1 **[open]** | `E(Q)` is infinite exactly when `Lam 1 = 0`; and `w = (-1)^n` whenever the rank is the number n | modularity, weak Mordell-Weil |
| **Ledger form** (`ledgerCard`) | a curve, a continuation, the prime data (the counts N_p) | the rank is r and the products `N_p / p` grow like `C (log p)^r` **[open]** | `BSDStatement W` | modularity; Goldfeld's theorem |
| **Low-rank slot** (`LowRank`, `open_of_lowRank`) | the BSD input | none: it is a filled slot | the card's open step holds whenever the order is at most 1 | Gross-Zagier, Kolyvagin, with modularity |

In IM the statement is made for **any number field** and uses the true rank in the extended naturals (no junk value when the group
is not known to be finitely generated). The older form, over Q only, is kept in the API instance. **Nothing is an axiom.** A part
answered R136a1 is a named hypothesis that the theorems using it carry (it is the statement itself); an `OpenStep` or `External` slot
of the API is likewise an ordinary hypothesis. Neither appears in an axiom audit.

## VII.3 What is proved

All of this is **[Lean]**. Three cautions come first.

1. **Audit.** The standard-axioms-only claim is not re-made in this draft. The axiom log of the API instance
   (`bsd-axioms.log`) was written before the instance was adapted today to the native core, and it still lists the earlier
   signatures (for example `BSDStatement` with a function argument). The native modules were not rebuilt for this draft either. The
   names below were checked against the source files, by reading, one by one. **Before the claim "standard axioms only" is made for
   the adapted instance, the log must be regenerated.**
2. **Inputs.** A result marked "from the named part" is a Lean theorem with the part as a hypothesis, not a proof of the part.
3. **No new theorem.** The proved structure is bookkeeping around classical facts. It shows the shape of the problem.

### VII.3.1 The algebraic side (`Arsenal.BSD.Algebraic`)

The group of points `Pts W` is Mathlib's group of nonsingular points with the point at infinity.

* **Mordell-Weil from weak Mordell-Weil** (`mordellWeil_of_weak`): if E(K)/2E(K) is finite, E(K) is finitely generated. The proof is
  Mathlib's descent theorem with the naive height. Weak Mordell-Weil (`WeakMordellWeil`) is a named part. **[Lean, from the named
  part]**
* **The torsion is finite**, with no assumption (`torsion_finite`, from Mathlib's `finite_torsion`). **[Lean]**
* **The rank** `algRank` is the rank of E(K) as a Z-module, in the extended naturals. It is the true rank whether or not E(K) is known
  to be finitely generated. It equals `Module.finrank` once E(K) is finitely generated, and is then finite (`algRank_eq_finrank`,
  `algRank_ne_top`).
* **Rank zero is finiteness** (`algRank_eq_zero_iff_torsion`, `algRank_eq_zero_iff`): the rank is 0 exactly when every point has
  finite order, exactly when E(K) is finite. No Mordell-Weil is needed: finite torsion is enough. And E(K) is infinite exactly when
  the rank is positive (`infinite_iff_algRank_pos`). **[Lean]**

### VII.3.2 The analytic side (`Arsenal.BSD.Analytic`)

* **The continuation as a property** (`IsContinuation`): a function analytic on a half-plane `re s > a` with `a < 1`, equal to
  Mathlib's L-series on some right half-plane. This is what BSD reads: the germ at s = 1, reached from where the series converges.
  An entire function that equals the series for `re s > 3/2` is one (`IsContinuation.of_entire`). A continuation is analytic at 1
  (`IsContinuation.analyticAt_one`). **[Lean]** That a continuation exists over Q is modularity **[external]**.
* **The order of the zero is well defined**: two continuations agree near s = 1 (`continuation_unique`, the identity theorem on a
  convex half-plane), so they have the same order there (`order_welldefined`). A zero exists exactly when the order is positive
  (`zero_iff_order_ne_zero`). **[Lean]**
* **The gamma factor** (`gammaFactor`; over Q it is `N^{s/2} (2 pi)^{-s} Gamma(s)`, `gammaFactor_degree_one`) is analytic and not zero
  at s = 1 (`gammaFactor_analyticAt`, `gammaFactor_one_ne_zero`). So the completed function has the same order as the L-function
  (`completed_order`). **[Lean]**
* **Parity** (`order_parity`, `order_parity_of_factor`, `analytic_parity`): if the completed function satisfies
  `xi(2 - s) = w xi(s)` near s = 1 (`FunctionalEquation`; the strip form implies it, `FunctionalEquation.of_strip`) and the order is
  a natural number n, then `w = (-1)^n`. The sign is not free: it is forced by the order. **[Lean, from the functional equation]**

In words: the mirror `s <-> 2 - s` fixes the parity of the order. It does not fix the order.

### VII.3.3 Point counts that run (`Arsenal.BSD.Count`)

`count W` counts the solutions of the Weierstrass equation over any finite ring, plus the point at infinity. `frobTrace W = q + 1 - count W`.
The decidable `hasseCheck W` is proved equal to the real inequality `abs(a) <= 2 sqrt q` (`hasseCheck_iff`). Over a finite field,
`count` is Mathlib's `Nat.card` of the group of points (`count_correct`), and at every prime of good reduction the count of the
curve read mod p is Mathlib's (`reduceMod`, `count_reduceMod`). Nothing is `noncomputable`: what runs is visibly computable. At
p = 5 the curve y^2 = x^3 - x has trace -2 and passes the check, both by the kernel (`decide`). **[Lean]**

### VII.3.4 Hasse, named, and what it gives (`Arsenal.BSD.Hasse`)

Hasse's bound at a place of good reduction, in Mathlib's own terms, is the named part `Hasse W` (with `LocalHasse` at one place).
Mathlib has neither isogeny degrees nor intersection theory on E x E, so the bound is not provable there yet. What follows from it
is proved:

* **The rotation bound** (`invQuad`, `invQuad_coeff`, `quad_bound`): if `a^2 <= 4q`, the coefficients `c_k` of `1/(1 - aT + qT^2)` obey
  `abs(c_k) <= (k + 1) q^{k/2}`. The proof is the rotation itself: `c_k` is a sum of `alpha^i beta^{k-i}` with both roots on the
  circle of radius `sqrt q`. At bad places `abs(c_k) <= 1` (`lin_bound`, `invQuad_bound`, `invQuad_bound_lin`). **[Lean]**
* **Every local factor of Mathlib's L-function is bounded** (`localPowerSeries_coeff_zero`, `localPowerSeries_coeff_bound`), and the
  first coefficient of `W.LFunction` is 1 (`eulerProduct_apply_one`, `LFunction_one`). **[Lean, from `LocalHasse`]**
* **A finite order**: an L-series with first coefficient 1 that converges absolutely somewhere is not zero for all large real
  arguments (`LSeries_not_eventually_zero`), so every continuation has a finite order at s = 1 (`order_ne_top_of_LSeries`,
  `order_ne_top_of_summable`). **[Lean]**
* **Through one more named part.** `EulerProductBound` says an Euler product whose local factors have these coefficient bounds
  converges absolutely for `re s > 3/2` (it is dominated by `zeta_K(s - 1/2)^2`) **[classical, recalled]**. With it, Hasse gives the
  convergence (`LSeriesSummable_of_hasse`), a finite order (`order_ne_top`), and parity with **no order given separately**
  (`analytic_parity_of_hasse`). **[Lean, from the named parts `Hasse` and `EulerProductBound`]**

### VII.3.5 The statement, and what follows from it (`Arsenal.BSD`)

`BSDStatement W` says: a continuation exists, and the rank equals the order of its zero at s = 1. It is a statement about W alone
(`bsdStatement_iff` turns it into the equation `rank = order` when a continuation is in hand). It is the **rank part of the Clay
statement** for K = Q, given the continuation **[paper]** (the identification of the Lean definition with Wiles' text is made in
prose here, not in Lean). From it:

* **The existence line** (`existence_line`): E(K) is infinite exactly when `Lam 1 = 0`. **[Lean, from BSD]**
* **Parity of the rank** (`rank_parity`, `rank_parity_of_fg`): with the functional equation, a rank equal to the number n gives
  `w = (-1)^n`. **[Lean, from BSD]**
* **A finite rank, and parity with no rank given separately** (`algRank_ne_top_of_hasse`, `rank_parity_of_hasse`): under BSD, Hasse and
  the Euler product bound, the rank is finite (it is the order of a zero) and `w = (-1)^rank`. **[Lean, from BSD and the named parts]**
* **The refined conjecture** (`RefinedBSD`): near s = 1, `Lam(s) = (s - 1)^r g(s)` with `g(1) = Omega Reg #Sha tam / (#tors^2 sqrt abs(d_K))`.
  The rank `r`, the torsion order and the field discriminant are derived. Mathlib defines none of the real period, the regulator,
  Sha or the Tamagawa product, so they stay free numbers in the statement. The refined statement gives the rank statement when its
  leading coefficient is not zero (`bsd_of_refined`). **[Lean]**

### VII.3.6 Hasse as an encoder, and the Euler ledger (`ProofPhase.API.BSD`)

* **The Frobenius eigenvalue** `alpha = a/2 + i sqrt(q - a^2/4)` has norm `sqrt q` exactly when `a^2 <= 4q` (`frobAlpha`,
  `frobAlpha_normSq`, `norm_frobAlpha`). The point count is `norm(1 - alpha)^2` (`count_normSq`). **[Lean]**
* **Hasse's bound is an encoder** (`frob`): the state `sqrt q` and the rotated image `alpha` share one root, and that shared root is
  Hasse's bound. The reflection coefficient is `a/(2 sqrt q)` (`frob_refl`). The Szego factor is `1 - a^2/(4q)`, in the unit
  interval (`frob_szego`). In angle terms: `cos theta_p` and `sin^2 theta_p`, the Sato-Tate density. **[Lean; Hasse as input]**
* **The ledger**. At each step (a prime) the factor is `N_p / p`. Hasse's bound puts it between `(1 - p^{-1/2})^2` and
  `(1 + p^{-1/2})^2` (`factor_bounds`, `EulerData.fac_bounds`). So the partial product keeps a margin (`EulerData.lower`) and has a
  chain bound (`EulerData.upper`, `P_le`). **No finite stage of the Euler product is zero** (`no_finite_zero`). A zero at s = 1 is a
  property of the whole chain, a rate, never of one step. **[Lean; Hasse as input]**
* **Care.** `EulerData` takes the counts as a bare sequence with Hasse as input. That the sequence is the counts of one given curve
  is documented in the structure and **not checked in Lean**. Checking it needs the link from Mathlib's local factor at the
  completion to the count over `Z/p`, at every prime. The link is routine and not stated. **[open as a formalisation item]**

### VII.3.7 The card and its conclusions (`ProofPhase.API.BSD`)

* **Without the open step** (`unconditional`): from the three `External` inputs of `Input`, E(Q) is finitely generated, its torsion
  is finite, every continuation has the same order at s = 1, and that order's parity is the sign. **[Lean, from modularity and weak
  Mordell-Weil]**
* **The card** (`problem`): open step `BSDStatement W`; conclusion the existence line and the parity of the rank. **[Lean]**
* **The low-rank theorem in its slot** (`LowRank`, `open_of_lowRank`): Gross-Zagier-Kolyvagin as an `External` fills the open step
  whenever the order is at most 1. **[Lean for the plumbing; external for the content]**
* **The ledger card** (`LedgerInput`, `ledgerCard`): from the growth `C (log p)^r` (open step) and Goldfeld's theorem (`External`),
  BSD follows. Goldfeld's theorem is true only when the prime data are the curve's own (see the care in VII.3.6). **[Lean for the
  plumbing; external for the content]**

### VII.3.8 The slot is not empty: y^2 = x^3 - x

The curve y^2 = x^3 - x (conductor 32, complex multiplication by i, Fermat's curve for the congruent number 1).

* The curve over Q and over Z; its discriminant is 64 and it is elliptic (`E32`, `E32_Δ`, `E32Z`, `E32Z_Δ`); the three points of
  order two are on it (`E32_points`). **[Lean]**
* The computed count mod p is Mathlib's at every odd prime (`count_E32`). The trace of Frobenius runs at the odd primes up to 37; it is
  zero at the primes that are 3 mod 4. The Hasse check runs by `#guard` at the odd primes up to 59, and at p = 5 it is proved by the
  kernel (`hasse_E32_five`). **[Lean]** (The notes say "below 100"; the source checks up to 59, and this part follows the source.)
* The known values enter as `External` inputs (`Data32`): continuation and functional equation (Deuring), `L(E, 1)` not zero, and E(Q)
  finite (Fermat's descent, E(Q) = the four points O, (0,0), (1,0), (-1,0)). **[external]**
* From them (`input32`, `bsd_E32`, `card_E32`): rank 0 equals order 0, BSD holds for this curve, the card's open step is filled, and
  the root number is +1. **[Lean, from the external values]**

Numerically (`bsd_check.log`, about 30 seconds on a CPU) **[numerical]**:

* For y^2 = x^3 - x (32a2): Hasse holds at all 2262 primes below 20000; the largest `abs(a_p)/(2 sqrt p)` is 0.99989.
  `L(E, 1) = 0.655514388573`. With the real period 5.2441151066, `L(E, 1)/Omega = 0.1250000000`. That equals the refined right-hand side
  `c_2 Sha / T^2 = 2 * 1 / 16` with the recalled values `c_2 = 2`, `Sha = 1`, `T = 4`. A number agreeing to ten digits does not prove
  `L(E, 1)` is not zero; the non-vanishing is the external input.
* For y^2 + y = x^3 - x (37a1, root number -1, rank 1): Hasse holds at the same primes. `L'(E, 1) = 0.305999773834`. The point (0, 0)
  has infinite order (the multiple 5P = (1/4, -5/8) is not integral, Nagell-Lutz). `L'(E, 1)/Omega = 0.0511114083`, against the recalled
  regulator 0.0511114082.
* The ledger `product of N_p/p` over `(log x)^r` at x = 100, 1000, 5000, 20000 is 1.65, 2.24, 2.12, 2.25 for 32a2 (target 2.157) and 6.82,
  6.79, 7.96, 7.19 for 37a1 (target 8.23). The products oscillate and converge slowly at the centre of the critical strip. The factor
  `sqrt 2` in the targets is the recalled constant of Goldfeld **[classical, recalled]**; the rank-0 numbers support it.

A computation can refute a statement. It never proves a for-all statement, and none is claimed.

## VII.4 What is borrowed

Every borrowed result is cited and marked. The project did not rebuild any of it.

| Borrowed | Where it enters | Status |
|---|---|---|
| **Modularity** (Wiles, Taylor-Wiles, Breuil-Conrad-Diamond-Taylor): continuation and functional equation of L(E, s) over Q | `Input.cont`, `Input.fe` | external |
| **Weak Mordell-Weil** (Mordell 1922, Weil 1929): E(K)/2E(K) is finite | `WeakMordellWeil` (named part in IM; `Input.weak` in the API) | classical |
| **Hasse's bound** (1933-36): `a_p^2 <= 4p` at good primes. Textbook proof: the degree is a positive definite quadratic form on End(E), so `deg(m - n phi) = m^2 - a m n + q n^2 >= 0` forces the discriminant bound (Silverman V.1.1). The same positivity is the Hodge index on E x E (Part VIII) | `Hasse` (named part); `EulerData.hasse` | classical |
| **The Euler product bound**: factors with the Hasse-type coefficient bounds give absolute convergence for `re s > 3/2`, dominated by `zeta_K(s - 1/2)^2` | `EulerProductBound` (named part) | classical, recalled |
| **Gross-Zagier, Kolyvagin** (with modularity): analytic rank 0 or 1 gives BSD | `LowRank` | external |
| **Goldfeld 1982**: the 1965 growth form of the Euler products implies BSD and the Riemann hypothesis for L(E, s) | `LedgerInput.goldfeld` | external |
| For the example: Deuring (continuation, CM), Fermat's descent (E(Q) is the four points), `L(E, 1)` not zero, recalled constants of the refined formula | `Data32` | classical / external |

The three named parts of IM (weak Mordell-Weil, Hasse, the Euler product bound) are classical theorems. A statement answered R136a1 is
placed outside the system and carried as a hypothesis by exactly the theorems that use it. It is not the same as "open".
The notes assess weak Mordell-Weil as within reach on Mathlib, Hasse as needing isogeny degrees or intersection theory on E x E, and
modularity as a very large formalisation **[paper, an estimate]**.

## VII.5 The one open step

**The open step of the card.** The BSD card has one open step: **`BSDStatement W`. The L-series of the elliptic curve continues to
s = 1, and the order of its zero there equals the rank of E(Q).** It is proved for order 0 and 1 by others (VII.4), with modularity.
**For order 2 and more it is open. [open]** Everything else in the card is proved (VII.3) or is a named external theorem (VII.4).

**What a proof would have to supply** (the two halves of an equality):

* a **construction** of r independent rational points from a zero of order r. No higher analogue of Heegner points is known.
  Candidates (derivatives of p-adic L-functions, Darmon's Stark-Heegner points) are conjectural; and
* a **bound** "rank <= order" beyond order 1 (Euler systems of higher rank, or Iwasawa main conjectures with non-degenerate p-adic heights).

**The stronger slot.** The ledger card's open step, the 1965 growth form of the Euler products, is strictly stronger. By Goldfeld it
also gives the Riemann hypothesis for L(E, s) **[external]**, which is part of GRH beyond Dirichlet L-functions. **[open]**

**The refined formula.** That the leading coefficient equals the full product of arithmetic invariants is also open in general. The
rank statement follows from it (`bsd_of_refined`). **[open]**

**Care points.**

* **The direction of the classical proofs.** The proofs do not run "points exist, so a zero by counting". At order 1 the zero **produces**
  the point (the Heegner point has height `L'(E, 1)` up to a factor). A nonzero value **forbids** points (Kolyvagin's Euler system
  bounds the Selmer group). So "the zero forces a point" is proved when the zero is simple and open from order 2 on. "A point of
  infinite order forces `L(E, 1) = 0`" is proved for every E/Q **[external]**; it is the contrapositive of Kolyvagin with modularity.
* **No finite stage sees the zero** (`no_finite_zero`). The order of the zero is decided by all primes together. A zero at s = 1 is not
  visible in any finite set of values `a_p`.
* **Two Riemann hypotheses, one proved.** Hasse's bound is the curve's local Riemann hypothesis, proved and an encoder. The Riemann
  hypothesis for L(E, s) is global and open. BSD itself does not need it; the ledger form of BSD would imply it.
* **Parity is free; size is not.** The functional equation fixes the parity of the order (`analytic_parity`). The order is the content
  and no symmetry fixes it.

**What this does to the problem.** The API does not settle BSD. It states BSD as a property of one equation, separates the proved
structure from the one open equality, and shows the slot is filled where the order is 0 or 1 and for the example above. The
mechanical answer is: **open, with the open step located, and the three classical parts that Mathlib lacks named.**

## VII.6 DMP readings attached to this part (all [reading])

Each reading is the owner's statement with its exact counterpart. None is mathematics.

* **BSD is IM: a full subset of only derivations.** Both sides of BSD are derived from one Weierstrass equation. The rank is a
  derivation of the rational points. The analytic side is a derivation of the point counts mod p. Unlike Yang-Mills (a measure),
  Navier-Stokes (initial data) or GU (hypercharges), the card takes **no content input**; its external slots are theorems about the
  derivations. So BSD is stated entirely in the vocabulary of IM (`Arsenal.BSD`). **Care:** this is a statement about form, not about
  settling. The rank equality stays open.
* **The zeros follow existence.** The order of the zero at s = 1 counts the independent rational points. Its exact counterpart has
  three levels: the existence line (`existence_line`), the rank equation, and the 1965 ledger form. The proved arrow runs by
  construction (Heegner) and exclusion (Kolyvagin), not by counting (VII.5).
* **Hasse is rotation at a DB.** In the owner's words, what stays open in the rederived core is "rotation at DB shaped". At the prime p
  (the DB) Frobenius acts as a rotation: its eigenvalue lies on the circle of radius `sqrt p`, and `cos theta_p = a_p/(2 sqrt p)` is the
  encoder's reflection coefficient (`frob`, `frob_refl`) **[Lean; Hasse classical]**. Its proof is one positivity: the degree form,
  or equivalently the Hodge index on E x E. The linear algebra of that is Part VIII's `weil_bound` at genus 1, where the conclusion is
  `abs(N - (q + 1)) <= 2 sqrt q`, which is Hasse's bound **[Lean for the linear algebra, from the intersection numbers and the Hodge
  index property, both external; the specialisation to one curve and the link of N to Mathlib's count are not made in Lean]**. So the
  open piece in Lean is one rotation per DB, confined by one positivity. It is open as a formalisation, not as mathematics.
* **What is left of BSD is the record, the `.cmb`.** In DMP the CMB is the observability layer: counts, never content. What the native
  core leaves open is exactly such a record: the refined formula's counts (the order of Sha, the Tamagawa product, the torsion) and
  measures (the period, the regulator). The refined conjecture says the leading coefficient over `Omega Reg Sha tam / (tors^2 sqrt abs(d_K))`
  is exactly 1: a dimensionless number whose logarithm is 0 **[classical statement, open]**. The functional equation carries both sides
  through the rotation `s <-> 2 - s` with sign `(-1)^rank` (`analytic_parity`, `rank_parity`) **[Lean]**. Dividing by `(s - 1)^r`
  removes the zero at the problem spot and leaves a finite nonzero value at the one box s = 1 (`bsd_of_refined`) **[Lean for the
  shape]**. The record balances numerically for y^2 = x^3 - x: `L(E, 1)/Omega = 0.125` against `2 * 1 / 16` **[numerical]**.
  **Care:** "the ratio is 1" is the refined conjecture itself, open in general. In Lean the five quantities are free numbers.
* **Where BSD sits in the triad.** Yang-Mills is existence, GRH is non-existence, NP vs coNP is their interaction (Part I). BSD is an
  equation between an existence count (independent points) and a zero count (the vanishing rate of the Euler ledger).

## VII.7 What would close it

If an independent proof supplied the construction and the bound for orders 2 and more, the card's open step would be discharged by
that work, and this part would supply the ledger skeleton and the audit. The change to this paper would be one row of the ledger,
one verdict line of this part and one item of the abstract. As the notes state it, nothing in this round proves any part of that.

The formalisation items that would change the status of the **borrowed** parts, none done:

1. Regenerate the axiom log of the adapted API instance, and run IM's own audit on the native modules.
2. Prove weak Mordell-Weil on Mathlib (Kummer theory, class groups and unit groups of the 2-division field), so `WeakMordellWeil` stops
   being a named part.
3. Prove Hasse's bound (isogeny degrees as a quadratic form, or intersection theory on E x E), so `Hasse` stops being a named part.
4. Prove the Euler product bound (the coefficients of an infinite Euler product, the residue fields of the completions as `O_K / v`, the
   convergence of `zeta_K` for `re s > 1`).
5. State and prove the link from Mathlib's local factor at the completion to the count over `Z/p`, at every prime, so `EulerData` is
   tied to one curve in Lean.
6. Modularity, a very large formalisation, stays an external input.
