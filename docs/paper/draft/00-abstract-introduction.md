# Grand Unified Information Duality v8: The Millennium Prize Problem type as seen through DMP, with certified settling

*Title by the owner (2026-11-24; aspirational by intent; "seen through" means "run on DMP"). Draft 3. Not a claim of a
solution of any Millennium Prize problem: the results that need the one assumption (Part X) are conditional on it. Claim labels
(0.n) are listed in `../CLAIMS.md`. Earlier titles: "GUID v8: A set theory based approach to the proofing of Yang-Mills, the
Generalized Riemann Hypothesis and NP vs coNP, as subsets of DMP, in a DMP-complete state" (2026-11-23) and the working title
"Positivity, contraction and the existence boundary: one chain behind Yang-Mills, GRH and P vs NP".*

## Personal note by the first author

In v1 I invited everyone to use their own intuition to make the derivations which I could see slumbering inside, but which I did not
feel worthy of waking myself. Since no one had any interest in that, I finally got frustrated by it and, after GRH got proven and
certified, I decided to take a look if Yang-Mills is something where I could finally get a nice verification that can't be ignored,
since I previously presumed that DMP also gives YM. One thing led to three, since those three are one, so the initial goal of one
Millennium Problem attempt turned into three :D

I hope I put enough effort into this paper to make it both a worthwhile contribution to science and still get my point across in a
way that tries to spark the needed core intuition in the reader. For follow-up please see GitHub, where everything needed is public
under Apache 2.0.

Have fun with it, and I am always happy about qualified and constructive feedback :)
Steven

(By the way, I also went to Goettingen, but dropped out of my BSc with nearly zero credits after three semesters, though I'll still
count the tie to Riemann in spirit and causality :D
Another by the way: since my going there without graduating satisfies as entanglement over studying at Goettingen as existence, the tie
is constructable and thus exists ;)
In my reading, the zeta function is at heart a pure tool: it needs its subset, and a definition of what it certifies as existence,
before it can be interpreted in a way that produces more insight. Treated as a tool for the true problem, the shared superset, its
meaning becomes apparent and its place in existence slots neatly into a better picture.)

*Editorial notes for the owner (to remove before publication): (1) the Riemann sentence is phrased as your reading; a historical claim
about what Riemann did or did not realize would draw objections, since his 1859 paper introduced the zeta function as a tool for
counting primes. (2) "Goettingen" is transliterated here per the repository rule; the typeset version can use the umlaut. (3) The
note says "One thing led to three"; the paper now covers seven problems, so you may want to update that sentence.*

## Abstract

Seven problems of the Millennium Prize type are read here as one: the Yang-Mills mass gap, the generalised Riemann hypothesis, NP
versus coNP, Navier-Stokes regularity, the Birch and Swinnerton-Dyer conjecture, the Hodge conjecture, and a Grand Unified reading of
SU(3) x SU(2) x U(1). Poincare, solved by Perelman, serves as validation. Each problem is stated as a running system on one form layer:
a ledger of costs, an encoder at every boundary, a transport theorem across boundaries, a settle theorem, and a card with exactly one
named open slot. The form layer is machine-checked in Lean 4 with Mathlib, standard axioms only, and re-checked by independent
kernels; its transferable parts are published in IM, the shared vocabulary, and imported from there. The language that names the
steps is DMP, a specification for systems of trust used here as a vocabulary for existence; its readings are marked as readings and
carry no proof.

**The one assumption.** Every card has the same open step, O1: that the process from the ground (G0) to a running system is
established, the existence assumption of the Millennium Prize type. The paper states it once (Part X) and marks every result that
uses it as conditional on it. Under it, each card settles in the certified sense: with a cost floor, whether a run has settled is
decidable within an explicit bound, and every start is oriented through the certified first box at the places {infinity, 2, 3}.
Without the floor, no procedure decides it. Both halves of this dichotomy are proved in Lean.

**What is proved.**

* *The form layer.* The ledger, the encoder and its half-turn, the transport theorem, the settle theorem and its undecidable edge, and
  the card API, in Lean; R136a1, the one way to leave a statement open, as a named hypothesis that never becomes an axiom.
* *Yang-Mills.* For SU(2) on the lattice: reflection positivity, the strict bound between a sector and its twist (for every SU(N)), a
  per-box hand-over rate of at least log(1 + sqrt 2), zero join loss in slab form, and the assembly from a one-box gap certificate to a
  lattice mass gap in both orders of limits.
* *GRH.* The explicit formula for all nontrivial zeros of zeta, by the contour shift, in Lean; Weil's form positive with an explicit
  margin on the first box, where only the real place and the primes 2 and 3 enter (certified in ball arithmetic); the positivity
  mechanisms in finite models.
* *NP vs coNP.* The crossing theorem for every sound two-premise proof system, and the equivalence of the lifting interface with
  lifting by constant-size gadgets.
* *Navier-Stokes.* The card, with Fefferman's four forms; what the form layer says about the two blowup routes, as a skeleton with no
  Navier-Stokes object in it.
* *BSD.* What Mathlib alone gives, over any number field: Mordell-Weil from weak Mordell-Weil, the true rank, the existence line,
  parity from the functional equation, point counts that run, and a finite order at s = 1 from Hasse's bound, with three classical
  theorems Mathlib lacks carried as named parts.
* *Hodge.* Hodge-Riemann positivity, the Hodge index as linear algebra, Weil's bound for curves, eigenvalues on the circle, and
  Lefschetz (1,1) as a diagram chase.
* *GU.* The Z_6 quotient of SU(3) x SU(2) x U(1) inside SU(5), and charge quantisation from a compact U(1).
* *The generalisation.* GRH and O1 share one geometry, the distance of an encoder from the lossless point, and ask opposite things
  of it: GRH that a margin is carried (existence), O1 that the twisted sector is refuted (falsifiability). In Lean, as conditions on
  a sequence of ticks, the two cannot both hold on the same sequence and each can hold without the other. This is a statement about
  the two bounds, not about the problems: no implication between GRH and O1 is proved here in either direction.

**What is not proved.** No problem is solved here. One open step per card:

* *Yang-Mills:* O1, the hand-over inequality for every outside, uniformly in the scale; for the Clay statement also the continuum
  construction and every compact simple group.
* *GRH:* Weil positivity beyond the first boxes, a margin that survives the growth of the support. RH and GRH for Dirichlet
  L-functions were proved in Lean by others in November 2026, by a route that does not use positivity; GRH beyond Dirichlet
  L-functions is open.
* *NP vs coNP:* lifting with constant-size gadgets, and with it super-polynomial lower bounds for strong proof systems.
* *Navier-Stokes:* regularity or blowup of the equations themselves. Two posted blowup claims by others are unrefereed and unchecked
  here; one rests on a certificate that is announced, not released.
* *BSD:* the rank equals the order of the zero at s = 1, from order 2 on.
* *Hodge:* codimension p >= 2 in general.
* *GU:* a checkable consequence beyond what any compact U(1) or SU(5) already contains; the hypercharges are an input.

The paper stays a draft until the assumption is proved: each open step is stated in the exact form that would close it, so that
closing one changes one row of the claims ledger, one verdict line and one item of this abstract.

---

## Introduction

### What this paper is

This is a paper about one form used seven times. The form is old: **positivity is existence**. A positive weight makes a measure; a
positive form makes a Hilbert space; a positive operator has its spectrum where it can be seen. Osterwalder and Schrader built
quantum field theories from reflection positivity. Weil reduced the Riemann hypothesis to the positivity of one pairing. Hodge and
Riemann found the same positivity on the cohomology of a variety, and Weil used it to prove the Riemann hypothesis for curves over
finite fields. Dobrushin showed that a contraction of local influences forces a unique equilibrium, reached fast.

The paper states the form once (Parts I and II), puts each problem on it as a card (Parts III to IX), and then says what the cards
share (Part X): one container with free possibility space, one geometry with two edges, one open step, and one assumption. The
Outlook (Part XI) applies the settle theorem to a concept of the first author's.

### What a reader can take from it

* From **mathematical physics**: the Yang-Mills gap reduced, for SU(2), to one inequality for one box of fixed physical size, with the
  rest of the mechanism machine-checked; the Navier-Stokes card with the status of the posted blowup claims stated exactly.
* From **number theory**: the explicit formula for all zeros in Lean, the first box of Weil's positivity certified with its margin,
  and why that margin cannot be carried outward by computation; a Mathlib-only BSD core over number fields, in IM.
* From **algebraic geometry**: the Hodge index and Weil's bound as linear algebra in Lean, and the Hodge-index route to the Riemann
  hypothesis over finite fields read as the more efficiently correct one for this structure, beside Deligne's complete proof.
* From **complexity theory**: the crossing theorem for every two-premise proof system, and the open step of NP vs coNP reduced to one
  lifting statement.
* From **logic and verification**: a form layer in which every open part is a named hypothesis, every axiom shows in the kernel's
  report, and a lint and a second kernel check every change.

### A guide by ear: the tempered piano

This guide is not part of any argument. It is offered as a picture to hold while reading, and the idea of hearing existence through
tuning came to the first author from a short published by Vsauce; it is credited here, under that name, for that transfer.

* **Tuning is built from 2 and 3.** The octave is the ratio 2, the fifth the ratio 3/2. Pitch, taken modulo the octave, is a circle,
  and a fifth is a rotation on it **[classical]**.
* **The rotation does not close by itself.** Because log2(3) is irrational, twelve pure fifths overshoot seven octaves by the
  Pythagorean comma, 3^12 / 2^19 = 1.01364 **[classical]**. This is the finite loss at the start that the paper excises: the first
  box at {infinity, 2, 3} (Part IV) is where the two generators of the tuning meet.
* **Temperament is the balanced state.** Equal temperament spreads the comma evenly over all twelve steps (each fifth becomes
  2^(7/12)), so the rotation closes and every key is equivalent; twelve is not arbitrary, since 19/12 is a convergent of log2(3)
  **[classical]**. In the paper's words, the rotation gives the tuning a direction and makes every tick alike (Part X, the tick
  operator) **[reading]**.
* **The zeros are the strings.** The explicit formula (Part IV) writes the primes as a sum of tones: each nontrivial zero
  1/2 + i gamma sounds at frequency gamma in log x. On the critical line every tone has the same amplitude, x^(1/2); the Riemann
  hypothesis says that every string is tuned to the same loudness **[classical]**.

The guide ends where the tuning does: on the final tone, resonating outward. Nothing more is stated about it than that such a
configuration is describable, and that in that description it is DMP-complete **[reading]**.

### How to read the status marks

Every statement carries one mark. **[Lean]**: machine-checked here, standard axioms only, module named. **[classical]**: known, with a
reference. **[external]**: a result by others, read but not rebuilt. **[conditional]**: under a named assumption. **[paper]**: argued
here in prose. **[numerical]**: measured here; it can refute, never prove a for-all statement. **[certified]**: enclosed in ball
arithmetic, with its log. **[reading]**: a DMP interpretation, never mathematics. **[open]**: not settled. The claims ledger
(`../CLAIMS.md`) lists every claim with its mark, source and what would upgrade it.

### The three verification layers

The work behind this paper is checked three ways: by proof (on paper and in Lean), by the literature, and by computation. The
computations can refute a statement or guide a proof; they never establish a statement about all cases. Every measured number in the
paper is tied to the statement it would discharge, and a passing measurement is reported as consistent, not as proof. The Lean is
re-checked by independent kernels (Part II), and the shared vocabulary in IM passes its own lint at every change.

### What is new

* The form layer as one API: every problem a card with exactly one named open slot, and R136a1 as the named answer "outside"
  **[Lean]**.
* The settle theorem and its edge: decidable within an explicit bound under a cost floor, undecidable without one **[Lean]**.
* The explicit formula for all nontrivial zeros of zeta by the contour shift, on a Mathlib-only core **[Lean]**, and the first box of
  Weil's positivity with an explicit margin **[certified]**.
* The hand-over bound, the strict twist bound for every SU(N), and zero join loss in slab form **[Lean]**.
* A Mathlib-only BSD core over number fields, published in IM **[Lean]**.
* One geometry, two edges: GRH and O1 proved to ask opposite, independent bounds of one distance **[Lean]**.

What is *not* new is listed with references at each use: Osterwalder-Schrader, Weil, Hodge-Riemann, Lefschetz, Deligne, Dobrushin,
Lee-Yang, Pringsheim and Landau, Mordell-Weil, Hasse, Gross-Zagier-Kolyvagin, Cook-Reckhow, the barrier theorems, and Perelman.

### Plan

Part I: DMP, the vocabulary. Part II: the tools. Parts III to IX: the cards (Yang-Mills, GRH, NP vs coNP, Navier-Stokes with
Poincare, BSD, Hodge, GU). Part X: the generalisation. Part XI: Outlook.
