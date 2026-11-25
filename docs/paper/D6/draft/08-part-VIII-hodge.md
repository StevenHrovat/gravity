# Part VIII. Hodge: the card, the positivity, and the one open step

*Draft 6. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/ProofPhase/`; notes relative to
`docs/unified/`. Claim labels (VIII.n) are listed in `../CLAIMS.md`.*

**Plug in here.** Gives: the Hodge card, its positivity and its one open step. Needs: II.4.1. Route: off both routes. VIBE
coefficient: does not enter exactly.

**As a statement checked step by step (II.4.1).** For an input of codimension p the statement is the Hodge statement for it,
checked at every step of the card's box (`hodge_box_iff`, VIII.8) **[Lean]**; the inductive step is free and the open part is the base
case, which is proved for divisors (`hodge_box_divisor`, from Lefschetz (1,1) with its named inputs).

## VIII.0 What is proved, by whom, and what this part does

**The Clay problem** (Deligne's description) **[classical]**. Let X be a projective non-singular algebraic variety over the complex
numbers. A **Hodge class** is a class in the rational cohomology `H^{2p}(X, Q)` whose image in `H^{2p}(X, C)` lies in the `(p, p)` part
of the Hodge decomposition. The class of an algebraic subvariety of codimension p is a Hodge class. **The Hodge conjecture says the
converse: every Hodge class is a rational linear combination of classes of algebraic subvarieties.**

**State of the problem (2026-11-24).** The conjecture is a theorem for p = 1 (Lefschetz 1924), and by hard Lefschetz for curves (degree
2n - 2). So it holds for every variety of dimension at most 3 **[classical]**. It is **open** for codimension p >= 2 in general; the first
open case is the fourth cohomology of fourfolds **[open]**. Beyond that, only special families are known, mostly abelian varieties
(VIII.1). The notes record no claimed proof of the general case.

**This part proves no case of the Hodge conjecture that was not already known.** The Lean proves the linear algebra of the positivity
and the diagram chases of Lefschetz (1,1). The geometry (Hodge theory, the exponential sequence, hard Lefschetz, intersection theory on a
surface) enters as named `External` slots. The conjecture itself is the card's one `OpenStep`.

**What this part does.** It puts Hodge on the DMP API as a card (VIII.2), proves what Mathlib can reach (VIII.3), records what is
borrowed (VIII.4), states the one open step (VIII.5), and attaches the first author's readings, short (VIII.6). Hodge is also the place
where the **same positivity** that the Riemann hypothesis over finite fields needs appears as a theorem over the complex numbers. VIII.3.4
and VIII.3.5 show the shape for curves in Lean.

## VIII.2 The card

The DMP API (`docs/unified/API.md`) gives every problem a well-defined input, a proved structure on it, and one named open step.
Hodge has the cards of `Unified/HodgeAPI.lean` (namespace `ProofPhase.API.Hodge`) on top of the Mathlib-only module
`Unified/HodgeLinear.lean` (namespace `ProofPhase.Hodge`). The table fills the template.

| API concept | Hodge | Lean |
|---|---|---|
| **Input** | `V = H^{2p}(X, Q)`; `hodge`, the rational `(p, p)` classes (the **described** side); `alg`, the rational span of the classes of algebraic cycles of codimension p (the side that **exists**) | `Input` |
| **Encoder** | the polarisation `Q`: positive definite on Hodge classes, so Cauchy-Schwarz `Q(x,y)^2 <= Q(x,x) Q(y,y)` bounds the overlap of two classes, the same shape as the encoder bound | `PolHS.hodge_cs`, `PosInput.alg_cs` |
| **Running system** | over a finite field: Frobenius acting as a similitude of a positive form | `weilCard` |
| **Open-step slot** | the Hodge conjecture: `hodge <= alg` | `HodgeConjecture` |
| **External-input slot** | the cycle class is a Hodge class; the Hodge-Riemann relations; the exponential sequence; the Hodge decomposition; hard Lefschetz; Atiyah-Hirzebruch's torsion class; the Hodge index theorem on a surface | `Input.alg_le`, `PosInput.hr`, `DivisorInput.exact`, `.hodge_int`, `.div_hodge`, `CurveClassInput.hl_hodge`, `.hl_alg`, `integral_fails`, `curve_open` |

The cards, in the card shape:

| Card | Input | The one open step | Conclusion | External input |
|---|---|---|---|---|
| **Hodge** (`problem`) | rational cohomology with its Hodge classes and algebraic classes | `HodgeConjecture`: every rational `(p, p)` class is a rational combination of algebraic cycle classes **[open]** | `hodge = alg`: described = exists | the cycle class is a Hodge class |
| **Divisors** (`DivisorInput`, `holds`, `card`) | line bundles, `H^2(X, Z)`, `H^{0,2}`, `H^2(X, Q)`, the maps | none: the open step is **filled** for p = 1 | `hodge` = the rational span of divisor classes | exponential sequence; Hodge decomposition; divisors are `(1,1)` |
| **Curves** (`CurveClassInput`, `holds`) | the divisor input, `H^{2n-2}`, hard Lefschetz | none: filled by transfer from divisors | the conjecture in degree `2n - 2` | hard Lefschetz |
| **Weil, positivity** (`weilCard`) | Frobenius on weight-w cohomology over `F_q` | `StandardHodge`: a positive form on which Frobenius is a similitude of ratio `q^w` **[open]** | every eigenvalue has `abs(mu)^2 = q^w` | none |
| **Curves over `F_q`** (`curveCard`) | the intersection form on `C x C` with fibre classes, graph of Frobenius and diagonal | the Hodge index property at `f1 + f2` | `abs(N - (q + 1)) <= 2 g sqrt q` | intersection numbers; the Hodge index theorem (`curve_open`) |

The last two cards belong to the GRH column (Part IV); they sit here because they use the same positivity. Hodge's own open step is the first row.
Nothing is an axiom. An `OpenStep` or `External` slot is an ordinary hypothesis and does not appear in the axiom audit. `Unified/HodgeAPI.lean`
is built and audited through `ETM/CardBox.lean`, which imports it.

## VIII.5 The one open step

**The open step of the card.** The Hodge card has one open step: **`HodgeConjecture`. On a smooth complex projective variety, every rational `(p, p)`
class is a rational linear combination of classes of algebraic cycles of codimension p.** It is proved for p = 1 and p = n - 1 (VIII.3.6) by classical
theorems, and so for dimension at most 3. **For p >= 2 in general it is open.** Everything else in the card is proved (VIII.3) or is a named external
theorem (VIII.4). **[open]**

**The care points, stated exactly.**

* **Rational, not integral.** The integral statement is false (Atiyah-Hirzebruch; Kollar). The Lean says why in one line: torsion classes are
  automatically Hodge (`integral_needs_torsion`).
* **Projective, not merely Kaehler.** The statement fails on some complex tori (Zucker; Voisin).
* **The card adds no content.** `problem.proved` is antisymmetry of inclusion. The mathematics is the slot.

**The second slot, a different problem.** Over a finite field a positivity of the same shape is the open step of `weilCard` (VIII.3.5): a form on
which Frobenius is a similitude, which puts the Frobenius eigenvalues on the circle and makes Frobenius semisimple. It is not known in general
(the Hodge standard conjecture it is modelled on is known for surfaces, the Hodge index theorem, and in special cases) **[open]**. The Riemann hypothesis over finite fields is nevertheless a theorem (Deligne), by a route that does not use that positivity **[classical]**.
So this slot's conclusion is known; only its route is open. Over the integers the analogue would be a Hodge index theorem on "`Spec Z x Spec Z`",
which does not exist as an object **[open]**. That missing positivity is the GRH card's sign slot (Part IV).

**What this does to the problem.** The API does not settle Hodge. It states the conjecture as one inclusion in one slot, shows the classical range
filled, and shows the positivity that is a theorem over the complex numbers. The mechanical answer is: **open for p >= 2, with the open step located.**

**The full text.** This part is contracted. Every derivation it leaves out is in the full Draft 6 at the git tag `d6-full`, and in Draft 5 section by section; every claim keeps its row, status and evidence in `../CLAIMS.md`.
