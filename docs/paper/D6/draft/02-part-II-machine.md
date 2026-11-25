# Part II. The machine, and the tools the problems use

*Draft 6, 2026-11-25 (machine-first). Contracted to the machine (II.0, II.3 to II.5), the chain of positivity (II.8) and what the tools do not do (II.16), with the tools of II.9 to II.15 in one line each. Lean paths are relative to `docs/mass-gap/formal/ProofPhase/`; claim labels (II.n.m) are listed in `../CLAIMS.md`.*

**Plug in here.** Gives: the machine and the headline theorem II.4.1, then the tools Parts III to V use. Needs: the core
page; the verify toy helps. Route: the exact route, stop 2. VIBE coefficient: a step of size 1/2 costs log 2 (II.0, C2)
**[classical]**; once each channel costs at least log 2, the Doeblin bounds sum to at least 1 (II.12.4) **[Lean]**; pointer jumping
leaves one layer after ceil(log2 d) halvings (II.15.2) **[Lean]**.

**Contracted.** Sections and labels this part names but does not print are in the full Draft 6, the git tag `d6-full`, and in Draft 5 section by section; every label is a row of `../CLAIMS.md` with its status and evidence.

**A. The machine.**

## II.0 The machine in ordinary terms: multiplication by complex numbers

**The translation.** In ordinary terms the machine is multiplication by complex numbers. Each step multiplies the carried amplitude
by one number c with |c| <= 1: its modulus is the gate factor (the ledger cost is its minus log), its phase the rotation. A run
multiplies its steps, so moduli multiply and phases add. If every |c| stays at or below some theta < 1, the run settles within an
explicit number of steps. If every |c| = 1 (pure rotation), the number never changes the mass, and a run of such multipliers is
decided by one comparison. The universal machine is a different running system that also has gate factor 1 everywhere, and for it
whether it settles cannot be decided (II.3). Everything else in this part (the ledger, the encoder, the settle theorem, the
one-box test) is a detail of this one picture.

### II.0.1 The complex-number ruleset

Nine rules carry the complex-number steps of the paper; the rest rests on the tools of Part II B (positivity, reconstruction, the
spectral theorem, contraction) and on the undecidability of II.3. Each rule is stated once here with a small example and where the
paper uses it, so that a reader who knows them reads "turn", "phase", "cost" and "half-turn" everywhere in the same sense (claim II.0i).

**The words.** A complex number $z = r e^{i\theta}$ has a *size* $r = \lvert z \rvert$, which the machine calls the *gate factor*, and an
*angle* or *phase* $\theta$. The *cost* of a step is minus the log of its size, $-\log r$; the ledger adds the floor $\delta$ to it
(II.1). A *turn* is a multiplication by $e^{i\theta}$; a *half-turn* is a multiplication by $-1 = e^{i\pi}$; a *full turn* is
$e^{2\pi i} = 1$. The turn in $N$ equal steps is $\zeta = e^{2\pi i/N}$, a primitive $N$-th root of unity: $\zeta^N = 1$ and no smaller
power is 1.

| Rule | Statement | Small example | Used in |
|---|---|---|---|
| C1 Multiplying is scaling times turning | for $z = r e^{i\theta}$ and $w = s e^{i\varphi}$ the product $z w$ has size $r s$ and angle $\theta + \varphi$: sizes multiply, angles add | $i \cdot i = -1$: two quarter-turns make a half-turn | II.0, every running system |
| C2 The cost is minus the log of the size | for $0 < \lvert z \rvert \le 1$ the cost $-\log \lvert z \rvert \ge 0$; sizes multiply along a run (C1), so costs add | size 1/2 costs log 2 a step; ten steps cost 10 log 2 | the ledger II.1, settling II.3, the free energies of III.3 |
| C3 Rotations add | $e^{ia} e^{ib} = e^{i(a+b)}$; on $N$ steps $\zeta^a \zeta^b = \zeta^{(a+b) \bmod N}$ | ROT13 twice is a rotation by 26, the identity; by 14 twice leaves 2 | T.5, II.2.8 |
| C4 A full turn averages to one exact value | for $\zeta = e^{2\pi i/N}$, $\frac1N \sum_{j<N} \zeta^{jk}$ is 1 when $N$ divides $k$ and 0 otherwise | the four quarter-turns $1 + i - 1 - i = 0$ | II.2.7 |
| C5 The mirror pairs the halves | $\overline{e^{i\theta}} = e^{-i\theta}$; for a function holomorphic near the circle with $f(\bar z) = \overline{f(z)}$ (real on the real axis) the $+$ half of a turn mirrors the $-$ half, and the result is real | $\cos\theta = (e^{i\theta} + e^{-i\theta})/2$ | II.2.7, the electric sectors of III.3.1c |
| C6 The turn back is the inverse turn | for $p(z) = \sum_{m<N} c_m z^m$, the average $\frac1N \sum_{j<N} p(\zeta^j)\, \zeta^{-jk}$ is $c_k$ | the full turn decodes its $N$ coefficients | II.2.8, III.3.1c |
| C7 The logarithm turns products into sums | $\log(xy) = \log x + \log y$, $\log x^k = k \log x$ for $x, y > 0$; for complex $z \ne 0$, $\log z = \log\lvert z\rvert + i \arg z$, so a product of steps becomes minus a sum of costs (real part) plus a sum of turns (imaginary part) | $\mu^k$ paths against $e^{-kF}$ cost: the series converges when $F > \log\mu$ | II.0 (decidability), III.5.4, R.7c |
| C8 Size-keeping maps are reversible | a complex-linear map of the line keeping every size is a unit multiplication; in more dimensions the size-keeping linear maps are the unitary ones, and on bits read as reals a reversible computation permutes the corner points, a unitary (permutation) matrix | ROT13 permutes the letters; a hash is not a permutation | II.0f, II.4.1, II.2.8 |
| C9 One turn around a point counts what is inside | one turn reads off a Taylor coefficient, $1/n!$, the order of a zero (a winding number), a leading coefficient | $1/n!$ is one turn of $e^z z^{-n-1}$ around 0 | II.2.7, IV.1.5c, VII.3.5f |

C7 in its complex form joins C1, C2 and C3: every multiplicative step of the real picture with a nonzero size becomes an additive one
in the complex picture, minus the costs adding in the real part and the turns in the imaginary part. Its one ambiguity is a whole number
of full turns: the complex logarithm is defined up to adding a multiple of $2\pi i$, which is why C4 and C9 read off exact values from
one turn. The first author reads this as being able
to simplify away the multiplicative steps of real mathematics into additive complex ones **[reading]** (claim II.0i).

**A run in polar form.** Three steps $z_1 = z_2 = \frac12 e^{i\pi/2}$ and $z_3 = \frac12 e^{i\pi}$. The run is their product: sizes
multiply to $1/8$ (C1), so the cost is $3 \log 2$, three steps of $\log 2$ (C2); angles add to $\pi/2 + \pi/2 + \pi = 2\pi$ (C3), one full
turn, so the product is the real number $1/8$. In logarithms the whole run is one sum, $-3\log 2 + 2\pi i$ (C7), and the $2\pi i$ is the
full turn that the product does not see.

**The encoder is the case N = 2.** With $\zeta = -1$ the two averages of C6 are the even part $(\psi + \psi')/2$ and the odd part
$(\psi - \psi')/2$, the mirror of C5; their ratio is the electric factor of II.2.2 (II.2.7).

**Where the rules stop.** Size 0 has no logarithm and no cost; $\arg z$ needs a choice of branch (C7); C5 and C9 need holomorphic
functions; C8's unit multiplication is for the line, unitary maps in more dimensions.

C1 to C9 are **[classical]**; their forms used in the proofs are **[Lean]**: C1 in `ETM/Complex.lean` (sizes multiply along a run,
`cmach_mass_eq`, II.0 above), C2 in the ledger of II.1, C3 as an instance in `rot_add` (on the string of Appendix T), C4, C6 and C9 in
IM's `Arsenal/FullTurn.lean`, C8 for the line in `rot_of_isometry` (II.0 above).

## II.3 The settle theorem and the decidability edge

**Why it clicks.** If every step pays a cost above the floor, the quantity must fall below any error bar, and one can count how long
that takes. If steps may pay exactly the floor, nothing forces it to fall, and nobody can tell in general whether it will.

**Running systems (II.3.1).** A *running system* with floor delta has states, a transfer step, an encoder factor in [0, 1] at each
state, a mass >= 0, and the ledger law mass(step x) <= e^delta fac(x) mass(x). The ledger theorems hold on every running system.
Running systems form a category in which the space of ledgers is the terminal object, so every running system has exactly one map
into it (its ledger). **[Lean]** (`ETM/RunSys.lean`, `RunSys`, `RunSys.carry`, `RunSys.contract`, `Hom`, `exists_unique_hom`,
`univIsTerminal`). The statements XI.2c of the Outlook (in the full text) rest on this.

**Theorem II.3.2 (settle).** In the *contraction class* (every factor at most theta, with e^delta theta < 1, which is exactly a
cost above the floor, for positive factors), the run from any state of mass at most M reaches balance within epsilon, by an
explicit computable number of steps: balanceBound M eps q = ceil(M q / (eps (1 - q))) + 1, for rational M, eps > 0 and q with
e^delta theta <= q < 1. So on this class the unbounded
question "does it settle?" is a bounded one. **[Lean]** (`ETM/Machine.lean`, `Contracting`, `contracting_iff_costAboveFloor`,
`balanceBound`, `balanceBound_ge`, `reaches_of_contracting`, `reaches_iff_bounded`, `reaches_of_contracting'`). The same statement
is XI.2a (in the full text).

**Theorem II.3.3 (the edge).** The machine that runs every partial recursive content is lossless: factor 1, cost = floor, outside
the contraction class. Whether it reaches balance is undecidable for all contents: no computable predicate decides it, and its
truth value exists (classically) but cannot be computed. **[Lean]** (`etm`, `etm_universal`, `etm_not_contracting`,
`etm_balance_undecidable`, `etm_truth_edge`; both sides in one statement, `etm_edge`). The same statement is XI.2b (in the full text).

**What it says in one line.** When every step pays a cost above the floor, settling is decidable within an explicit bound. When
steps may pay exactly the floor there are systems (the universal machine) for which it is not; a lossless system as such need not be undecidable (II.0). The step from the second case to
the first is the open step of every card (Part X, sections 4 and 5).

**One step, one `decide`.** The first author's definition: a DMP-complete proof is lintable in one step, relying only on `decide`.
The exact part is the computable layer of the machine: every decision has a computable form on rational data, proved right for the
real system once (`szegoQ_cast`, `elecQ_cast`), and an instance is then one kernel evaluation, for example
`balanceBound 1 (1/1000) (1/2) = 1001` **[Lean]**; the one-box certificate is one step at the shared gate plus induction (II.4).
So a finished, DMP-complete proof has its last step a single `decide` on finite data, with its correctness theorem proved once in
general **[reading]** (claim II.4f). Care points: the correctness theorems are ordinary Lean proofs over the reals, not `decide`
alone; the open steps are not of this form (O1 is a for-all over every outside, not one finite check); and `native_decide` stays
excluded, since the kernel itself must check the step.

**Existence is free, construction costs.** The first author's one-line summary of the machine: being in the state space costs
nothing; reaching a state costs a step, and every step pays at least the floor **[reading]** (claim II.3.4). It is the shape of the
ledger law (II.3.1) and of the one-box test, where sharing the gate is free and the content is that the marker travels with it
(X.68b). A hash is the same shape in a third setting: the hash was computed from some content, so a preimage exists, and checking
a supplied one is a single forward step; finding one from the hash alone is the costly direction **[classical]**. Nothing in this
paper weakens an established hash or cipher: no result here gives a way to invert one, and the reading agrees with their
one-wayness. That one-wayness stays what it is in the literature, a well-tested assumption rather than a theorem: that any one-way
function exists is open and would imply P != NP **[classical]**. The Clay statements ask for existence and construction, which is why
their cost sits in the construction step, O1 for Yang-Mills.

**The three applications.** Yang-Mills: the floor is the cost above log mu, and keeping it uniform in the cutoff is O1. GRH: the
margin decays without a floor (zero slack, II.1.5), so only the sign is decided scale by scale. NP vs coNP: a constant cost per
hidden variable is a floor.

---

## II.4 The one-box test

**The reading.** The author's sharpening: a box needs no outside, because every confinement has one shared gate at the DB. It
needs one command, step forward, the universal tick, which can simulate everything. If the step produces the wrong R136a1 marker,
the box is not DMP-complete; if the marker is correct, it is **[reading]**.

**The definition.** In Lean (the rotation API, in IM's arsenal, `Arsenal/Rotation.lean`, with the running-system version in
`ETM/Rotation.lean`): a box has one command, a gate factor, a margin and a marker per step, inside or R136a1; the marker is correct
when it agrees with the gate's own factor, and DMP-complete means correct at every tick **[Lean]** (claim II.4a). The smallest example
is the verify toy: on 8-bit words stepping by 2 with the marker "even" the box is DMP-complete, stepping by 1 it is refuted at tick 1
(T.1 to T.3) **[Lean]**.

**The outside.** The outside is read through the same gate by the half-turn: in the generic API the agreement of the two readings is
the gate's law (a field of `Box.Gate`), and in the plaquette layer it is proved: for a closed Z/2 layer the flux read from a box and
from its complement agree **[Lean]** (claim II.4b).

**The care point.** The test has content only when the marker is the system's own claim; a marker read off the gate afterwards always
passes **[Lean]** (claim II.4c).

**Where each problem's box is treated.**

| Problem | Section | Its box |
|---|---|---|
| Yang-Mills | III.12 | the gate factor is the best one-box ratio at each lattice level |
| GRH | IV.8 | the card box of its open step |
| P vs NP | V.10 | the card box of its open step |
| Navier-Stokes | VI.8 | the model box, built from the energy bound alone |
| BSD | VII.8 | the card box of its open step |
| Hodge | VIII.8 | the card box of its open step |
| GU | IX.8 | the tick box of charge quantisation |
| all, with the one assumption | Part X 4.4 | the one-box and scale certificates |

**The certificates.** The one-box certificate (one step at the shared gate certifies every tick), the scale certificate from the
sharing, and the universal machine as a box are stated with the one assumption in Part X 4.4 (claims X.68 to X.68c) **[Lean]**.

**Rigidity as a box.** Rigidity is one-box testable too: a manifold's presentations with its self-equivalences acting make a box that
is DMP-complete exactly when the manifold is rigid (rigid here is the structure-set condition: every presentation is the manifold seen
through a self-equivalence; its identification with a given manifold is the user's input), and the manifold is rigid if its box shares
the gate with a certified box, the sharing being the named hypothesis R136a1 "the gate is shared across scales", never proved (IM,
`Arsenal.Rigidity`) **[Lean]** (claim II.4d; G2 in Appendix A.5).

**Cards as boxes.** Every card is also a box: the tick box passes exactly when the statement of every tick holds, and the card box
exactly when the card's open step holds, and then gives the card's conclusion; it restates the step and proves no new bound **[Lean]**
(`ETM/CardBox.lean`, claim II.4e).

### II.4.1 Restatement and induction: the front door

In familiar terms: a problem is restated as one statement checked at every step of a sequence, and the restatement holds exactly
when the statement holds at every step. A proof then has the shape of an induction: a base case and an inductive step. In DMP's
terms a system with states, one step and its own claim at each state is an *observable system*; its restatement is its *one-box
description*, a box of the same API whose marker always asserts the claim (*inside*) and whose gate reads whether the claim is true,
so the box is correct at a state exactly when the claim holds there (`correct_iff`). The marker is the claim asserted, never read
off the gate: the self-marked box, whose marker is the gate's own verdict, always passes and says nothing (II.4c, `selfMarked_complete`),
and this box is its opposite. The claim is a decidable proposition; decidability is classical here, so this is no restriction:
every proposition is an observable system with one state.

**What each word buys** **[Lean]** (IM, `Arsenal/Observable.lean`; claim II.4g):

* *Restatement* (`box_complete_iff`): DMP-complete from a start exactly when the claim holds at every step. By definition; it proves
  nothing by itself.
* *Induction* (`route`, exact along the run `route_iff`): the base case (the claim at the start) and the inductive step (a step that
  keeps the claim) give the claim at every step. This is induction on the step; a proof of this shape exists exactly when the claim
  holds along the run, so the shape says what must be shown, not that it can be.
* *Every scale* (`route_everywhere`): where every scale's box is mapped onto the one box by a map that keeps the step, the gate and
  the marker (the shared gate, the named hypothesis R136a1), the induction shown once holds at every step of every scale. The
  content of this part lies in the map: in the verify toy the parity argument for k bits sits in the map onto one bit (T.2).
* *Falsifiable* (`refuted_by_tick`): one step where the claim fails refutes it.

When the observation is a reading against a margin (`ofReading`) and the reading is a coefficient hidden in a sum of N powers of a
root of unity, one full turn computes it exactly, so the check can be read by one turn (`turn_gate`, II.2.7). Two systems run side by
side give a system whose inductions combine (`prod`, `route_prod`) **[Lean]**, so a larger proof is the parts reassembled as the API
guides.

**Binary data, read as real numbers.** Read the bits {0, 1} as real numbers, so that the n-bit strings are the 2^n corners of
the n-dimensional cube; taken as basis vectors they span a space of dimension 2^n. A reversible computation permutes them, a
permutation matrix and so a unitary map over the complex numbers, so complex mathematics, the
full turn included, applies to it exactly; and every computation can be made reversible by keeping its history **[classical]**
(Bennett 1973; Toffoli 1980) (claim II.4h). Care point: the history is the supplied input. A reversible version of a hash runs
backwards only with the input it kept; a digest alone is not undone (R.6a, T.6).

**Where the open part sits, problem by problem** (claim II.4g for the Lean column; the reading of the two boxes with a gate factor
of their own as observable systems is **[paper]**, since they are gravity's own box type and no Lean bridge to IM's is written):

| Problem | Statement checked step by step | Lean box | Open part | Lean link |
|---|---|---|---|---|
| III Yang-Mills | the level criterion at every lattice level from k0, for some cell geometry and margin | `ymBox` | the inductive step, level to level: O1 (`FineOneBox`, equivalent in Lean, `fineOneBox_iff_complete`) | [paper] for the reading |
| III Yang-Mills card | the chain form `YMOneBox` at every step | `cardBox` | the base case | `tickBox_observable` |
| IV GRH | the sign at every scale (`ScaleSign`) at every step | `cardBox` | the base case | `tickBox_observable` |
| V NP vs coNP | the crossing cost (`CrossingCost`) at every step | `cardBox` | the base case | `tickBox_observable` |
| VI Navier-Stokes, three cards | route I's `PeriodContraction`; regularity; the A/B dichotomy (VI.2) | `cardBox` | the base case, not assumed by the paper | `tickBox_observable` |
| VI model box | the energy-only factor within the margin at every dyadic scale | `nsBox` | fails at some scale: the energy ledger refuted as a certificate, not regularity | [paper] for the reading |
| VII BSD | BSD for the curve at every step | `cardBox` | the base case | `tickBox_observable` |
| VIII Hodge | the Hodge statement for the input at every step | `cardBox` | the base case, proved for divisors | `tickBox_observable` |
| IX GU | charge quantisation at every step | `tickBox` (a box, no card) | none in the box: it passes, proved; the GU open step lies outside it (IX.5e) | `tickBox_observable` |
| Appendix T | an even word at every step, at every bit width | IM's box | none: base case, inductive step and the map of scales all proved | native |
| Trusted hashes (R.6b) | each trusted hash: back and forth deliver the same value | no Lean box: a check item by item, with no induction | none: every item checked, 9 proofs pass; the canary first tests the tools | [paper] |

So the proof has one shape everywhere, and the parts show where its open part sits: the base case on the cards, the inductive step on
the Yang-Mills box. Appendix T runs all of it on binary words. Figure 1, on the core page of the introduction, shows the shape once.


## II.5 The API: cards

**Why it clicks.** The form layer says nothing about content, so every problem can use it. Every problem has the same shape: an
input, a proved structure, one named open step.

**What the API gives (II.5.1).** One import, `ProofPhase.API`, a facade over the form layer: it moves and renames nothing, and its
theorems are re-exports or one-line wrappers. It has one structure per concept **[Lean]** (`API.lean`):

| Concept | In Lean | You supply | You get for free |
|---|---|---|---|
| a running system | `RunSys` | states, step, factor, mass, the ledger law | `carry`, `contract`, `decay_cost` |
| the settle bound | `settle`, `settle_everywhere`, `settle_iff_bounded`, `balanceBound` | the contraction class | an explicit step count |
| the decidability edge | `edge` | nothing | decided above the floor, undecidable at it |
| a chain with costs | `Chain` | a quantity, costs, the step law | `Chain.ledger`, `Chain.decay`, `Chain.summable`, `Chain.size` |
| a margin that survives | `Margin` | shares kept | `Margin.survive`, `Margin.pos` |
| an encoder | `Encoder`, `szegoFactor`, `elecFactor`, `cost` | a state and its rotation | the Szego factor in [0, 1] (`szegoFactor_mem`); the electric factor is `elec (Re c)` |
| an uncertainty | `Uncertainty` | error, factor, fresh uncertainty | `bounded`, `critical`, `sign` |
| the problem card | `Problem` | input, `Open`, `Concl`, `proved` | `Problem.holds` |
| the open-step slot | `OpenStep "name" P` | the one statement `P` | `P` itself, labelled |
| the external-input slot | `External "source" P` | a theorem from the literature | `P` itself, labelled |

The slots are transparent: `OpenStep "..." P` *is* `P`, so a theorem takes it as an ordinary hypothesis. Nothing is ever an axiom.
The labels make the open steps and outside dependencies greppable.

**Adding a problem (II.5.2).** Seven steps: copy the template (`API/Template.lean`, a worked toy); write the input; fill a running
system, chain or margin and check the one ledger inequality; write the open step in its slot; call the free theorems; add an
uncertainty if the input is only approximate; state the card. **[paper]** (the procedure; `docs/unified/API.md`, 3). The three
cards of Parts III to V are `API/YangMills.lean`, `API/GRH.lean` and `API/NP.lean`, each proved as "open step gives conclusion"
**[Lean]**; each open step is **[open]** (III.5.6, IV.4, V.6: `CrossingCost`, with V.4.10 the nearest concrete target). A
problem may have several cards: Navier-Stokes has three (VI.2), BSD three (VII.2), Hodge five (VIII.2); GU has a box and no card
(IX.2). The GRH card is a card for a finite model of zeros (its
open step `ScaleSign` is the sign at every scale of that model); the link to zeta is `tie_in`, which takes the statement of the
Riemann hypothesis as an `External` hypothesis. The toy settles in 101 steps to 1/100 (`toy_settle_101`)
**[Lean]**.

**What runs and what is truth only (II.5.3).** The settle count, the encoder factors on rational data and the ledger law on
rational data are computable and decidable: `balanceBound`, `szegoQ`, `elecQ`, `PaysQ`, `settle0`, with `szegoQ_cast`,
`elecQ_cast` and `PaysQ.pays` proving them right for the real system; the machine's step and balance test are primitive recursive
(`estep_primrec`, `halted_primrec`). The real-valued structures and the undecidability on the lossless side are truth statements,
not computed. **[Lean]** (`API.lean`).

**One consequence for every instance (II.5.4).** G0's phase field is one compact circle. Every continuous character of the circle
is z -> z^n for an integer n, so every label carried on it has integer charge, with no further assumption. **[Lean]**
(`API/Phase.lean`, `chargeQuantisation`, `PhaseLabel.integer_charge`; classical content: Pontryagin duality for the circle).

**What it does not do (II.5.5).** It proves no open step and adds no mathematics. It does not turn a problem into a running
system for you: the structure and its one inequality are the work. Arguments that use only the interface cannot settle P vs NP
(relativization, V.7), and the NP card inherits that. **[paper]**

---

## II.8 One chain, the first three problems

The first three problems (Parts III to V) run along the same four links.

> **positivity -> a space -> an evolution on it -> a spectrum that the positivity pins**

| Link | Yang-Mills | GRH | P vs NP (sampling side) |
|---|---|---|---|
| 1. Positivity | reflection positivity of e^{-S} | Weil's pairing W(f * f~) >= 0 | positive weights on assignments |
| 2. Space | the Osterwalder-Schrader (OS) Hilbert space | the GNS space of Weil's form | L2 of the Gibbs measure |
| 3. Evolution | the transfer matrix e^{-H}, H >= 0 | translation in log-scale | the heat-bath operator, 0 <= P <= 1 |
| 4. Spectrum | gap = decay rate of correlations | real spectrum = zeros on the line | gap = fast mixing |

**Why it clicks.** Links 2 to 4 are free once link 1 is given: they are theorems of the same pattern in each column (the reflection
step is the Lean form for Yang-Mills, the finite Weil criterion for GRH, the finite spectral measure for the sampling side; II.9 to
II.10 give each). The whole
difficulty of each problem sits in link 1 for the hard case (Yang-Mills: a certificate at one scale; GRH: positivity itself; P vs NP:
the step from a certified class to all inputs). The rest of this part makes links 2 to 4 precise and adds the four tools that act on
link 1 or carry it across scales.

---

**The tools, in one line each.** Positivity builds a space (II.9), pins the spectrum (II.10) and locates singularities (II.11);
contraction and data processing carry a bound down a chain (II.12); a strict sign gives a rate at the self-dual point (II.13); the
dichotomy of local, crossing flux and residue sorts refutations (II.14); and the native method optimises within a class (II.15).
Each is stated and proved as its ledger rows say; the ledger (II.1), the encoder and the full turn (II.2), the arsenal (II.6) and
the independent re-check (II.7) are in the full text.

## II.16 What the tools do not do

None of II.9 to II.15 creates positivity. Each starts from a positive weight, a positive pairing, a positive cost or a strict sign,
and carries it: into a space, into a spectrum, across a chain, across a boundary, down to a floor. The open step of each problem is
the place where that starting positivity is known locally, or in a model, and must be established for every case. Part X states
this once (section 4). The six sections II.1 to II.6 are the *form layer*: the part of the machinery that says
nothing about content and so serves every problem. II.16 holds for them too.

---
