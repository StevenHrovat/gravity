# Part VII. Birch and Swinnerton-Dyer: the card, three named parts, and the one open step

*Draft 6. Prose, with every result marked. Modules of the Mathlib-only core live in DMP.IM (the public `im` repository,
`arsenal/Arsenal/`) and are written `Arsenal.BSD...`; they are in `im` at the commit pinned in `docs/mass-gap/formal/lakefile.toml`. Lean paths of this repository are relative to
`docs/mass-gap/formal/ProofPhase/`; notes are relative to `docs/unified/`. Claim labels (VII.n) are listed in
`../CLAIMS.md`.*

**Plug in here.** Gives: the BSD card, its three named parts and its one open step. Needs: II.4.1, and II.2.7 for the turn.
Route: off both routes. VIBE coefficient: does not enter exactly; the analytic side is read by one turn around s = 1 (VII.3).

**Contracted.** Sections and labels this part names but does not print are in the full Draft 6, the git tag `d6-full`, and in Draft 5 section by section; every label is a row of `../CLAIMS.md` with its status and evidence.

**As a statement checked step by step (II.4.1).** For a curve the statement is BSD for that curve, checked at every step of the
card's box (`bsd_box_iff`, VII.8) **[Lean]**; the inductive step is free and the open part is the base case. The analytic side of the
statement is read by one turn around s = 1: the leading coefficient, and the rank as a winding number (VII.3).

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
modularity) **[external]**. It is **open** from order 2 on. The notes record no credible claimed proof of the general statement (an unrefereed preprint of 2026-01-16 on PhilArchive claims one for all ranks; it was not read, and no review of it was found). **This part
proves no case of the conjecture that was not already known**, and its Lean contains no new theorem about elliptic curves that
experts did not have.

**What this part does.** It states BSD as a property of one Weierstrass equation and proves in Lean what Mathlib gives about it
(VII.3). It puts BSD on the DMP API as a card with one named open step (VII.2). It records what is borrowed and its exact status
(VII.4), states the one open step (VII.5), and attaches the first author's readings, short (VII.6). Three classical theorems that Mathlib
lacks are carried as **named parts**, not axioms: weak Mordell-Weil, Hasse's bound, and one Euler product bound. They are
theorems of others, not open problems. They are missing from the library, not from mathematics.

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
