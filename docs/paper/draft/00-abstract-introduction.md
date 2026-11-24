# Grand Unified Information Duality v8: The Millennium Prize Problem type as seen through DMP, with certified settling

*Draft 4, machine-first. Not a claim of a solution of any Millennium Prize problem: the results that need the one assumption (Part
III) are conditional on it. Claim labels (0.n) are listed in `../CLAIMS.md`.*

## Personal note by the first author

In v1 I invited everyone to use their own intuition to make the derivations which I could see slumbering inside, but which I did not
feel worthy of waking myself. Since no one had any interest in that, I finally got frustrated by it and, after GRH got proven and
certified, I decided to take a look if Yang-Mills is something where I could finally get a nice verification that can't be ignored,
since I previously presumed that DMP also gives YM. One thing led to three, since those three are one, so the initial goal of one
Millennium Problem attempt turned into three :D

I hope I put enough effort into this paper to make it both a worthwhile contribution to science and still get my point across in a
way that tries to spark the needed core intuition in the reader. For follow-up please see GitHub, where everything needed is public
under Apache 2.0.

My logical deduction chain: Albert Einstein's description of existence was so perfect, that it allowed me to construct a
non-existence around it until its containment was inevitable, therefore bringing both into balance.

Have fun with it, and I am always happy about qualified and constructive feedback :)
Steven

(By the way, I also went to Goettingen, but dropped out of my BSc with nearly zero credits after three semesters, though I'll still
count the tie to Riemann in spirit and causality :D
Another by the way: since my going there without graduating satisfies as entanglement over studying at Goettingen as existence, the tie
is constructable and thus exists ;)
In my reading, the zeta function is at heart a pure tool: it needs its subset, and a definition of what it certifies as existence,
before it can be interpreted in a way that produces more insight. Treated as a tool for the true problem, the shared superset, its
meaning becomes apparent and its place in existence slots neatly into a better picture.)

## Abstract

Seven problems of the Millennium Prize type are read here through one test: the Yang-Mills mass gap, the generalised Riemann
hypothesis, NP versus coNP, Navier-Stokes regularity, the Birch and Swinnerton-Dyer conjecture, the Hodge conjecture, and a Grand
Unified reading of SU(3) x SU(2) x U(1); the Poincare conjecture, solved by Perelman, serves as validation. Each problem becomes a box
with one command, a step at one shared gate. Every step gives a marker, inside or outside, and the box is DMP-complete when every
marker agrees with the gate. In ordinary terms the machine under the test is multiplication by complex numbers of modulus at most one:
the negative logarithm of the modulus is the cost, the phase is the rotation. The machine, the test and the cards are checked in
Lean 4 with Mathlib on the standard axioms. DMP, a specification for systems of trust, supplies the vocabulary; its readings are
marked as readings and prove nothing.

No problem is solved here. One certifiable step is the same on every card: the step of the box at its gate, tested marker by marker.
The paper states one assumption, once and as a reading: that on five cards (Yang-Mills, GRH, NP versus coNP, BSD, Hodge) the box is
DMP-complete, its gate shared across scales; in each card's own terms this is a different open statement. Proved without it:
the reduction of the SU(2) lattice mass gap to one inequality on one box of fixed size, the explicit formula for all
nontrivial zeros of zeta, a crossing theorem for sound two-premise proof systems, and Mathlib-only cores for BSD and the Hodge index;
Weil's positivity on a first box, where only the real place and the primes 2 and 3 enter, is certified with explicit margins. In
the energy-only model the Navier-Stokes box gives a wrong marker, so that card is not DMP-complete; the Grand Unified box passes.
Each open step is stated in the form that would close it.

---

## Introduction

### What this paper is

This is a paper about one machine and one test, used seven times. The form under them is old: **positivity is existence**. A
positive weight makes a measure; a positive form makes a Hilbert space; a positive operator has its spectrum where it can be seen.
Osterwalder and Schrader reconstructed quantum field theories from reflection positivity. Weil reduced the Riemann hypothesis to the positivity
of one pairing. Hodge and Riemann found the same positivity on the cohomology of a variety, and Weil used it to prove the Riemann
hypothesis for curves over finite fields. Dobrushin showed that a contraction of local influences forces a unique equilibrium, and later work showed it is reached fast.

What is new is the shape put around it. A running system pays a cost at every boundary; with a floor its settling is decidable within
an explicit bound, and at no floor there are systems, the universal machine among them, for which no procedure decides it. A box with
one command at one shared gate is tested step by step, and it passes when every marker agrees with the gate. Each problem becomes
such a box. One certifiable step is the same on every card: the step of the box at its gate. On five cards the paper reads the open
step as one statement, that the card's box is DMP-complete, its gate shared at every scale **[reading]**; mathematically each is a
different statement, and the paper assumes it once (Part III). Navier-Stokes is the expected negative, and the Grand Unified card's
open step lies outside its box. The paper proves the machine and each box's core.

### Results and open steps

The results, by the problem they serve. Every Lean result names its module in the part that states it; "from X" names the inputs
it rests on.

* **The machine** **[Lean]**. The ledger, the encoder and its half-turn, the transport theorem, the settle theorem and its undecidable
  edge (for the universal machine, over all content), the one-box test with its one-box and scale certificates, and the card API.
  The one-box certificate needs a marker correct at the start and kept by the step at every state. In IM's arsenal, R136a1 is the
  one way to leave a statement open, a named hypothesis that never becomes an axiom; this repository's cards use the same
  transparent form under the names `OpenStep` and `External`.
* **Yang-Mills** **[Lean]**, for SU(2) on the lattice: reflection positivity, the strict bound between a sector and its twist (for
  every SU(N)), a per-box hand-over rate of at least log(1 + sqrt 2) (from positivity of the twisted partition function, a stated
  hypothesis), zero join loss in slab form, and the assembly from a one-box gap certificate to exponential decay of slab
  correlations (a lattice mass gap) in both orders of limits; the step to a gap of the Hamiltonian is argued in prose (IV.2.7). The
  open step in the form the assembly uses is `FineOneBox`; the box test restates it: `FineOneBox`, and O1 in chain form, hold
  exactly when the Yang-Mills box is DMP-complete (a restatement by construction; no new bound).
* **GRH.** The explicit formula for all nontrivial zeros of zeta, by the contour shift **[Lean]**. Weil's form positive with an
  explicit margin on the first box, where only the real place and the primes 2 and 3 enter: **[certified]** for the enclosures in
  ball arithmetic, **[paper]** for the analytic estimates that tie them to Weil's form (a working note, not independently read).
  Connes and Consani proved Weil positivity for test functions supported so close to 1 that only the real place enters, after
  Yoshida's work on the same Hermitian forms **[external, recalled]**; the first box here is the next range, with the primes 2 and 3
  and explicit margins. The positivity mechanisms in finite models **[Lean]**.
* **NP vs coNP** **[Lean]**. The crossing theorem for every sound two-premise proof system, on expanding, minimally unsatisfiable
  formulas, and the equivalence of the lifting interface with lifting by constant-size gadgets (VI.4.11).
* **Navier-Stokes.** Three cards on the form layer; there is no Navier-Stokes object in the Lean, and Fefferman's forms (A) and (B)
  are named, not defined. In the energy-only model the box gives the wrong marker at some scale, so it is not DMP-complete
  **[Lean]**.
* **BSD** **[Lean]**, from what Mathlib alone gives, over any number field: Mordell-Weil from weak Mordell-Weil, the true rank, the
  existence line, parity from the functional equation, point counts that run, and a finite order at s = 1 from Hasse's bound, with
  the classical theorems Mathlib lacks carried as named parts.
* **Hodge** **[Lean]**, the linear algebra of the positivity from named classical inputs: from the Hodge-Riemann relations (an
  input), positivity on Hodge and algebraic classes; the Hodge index as linear algebra; from the Hodge index property (an input),
  Weil's bound for curves; eigenvalues on the circle; and Lefschetz (1,1) as a diagram chase.
* **GU** **[Lean]**, a box, not a card: the Z_6 quotient of SU(3) x SU(2) x U(1) inside SU(5), charge quantisation from a compact
  U(1), and anomaly cancellation (with q_Q > 0 and coprime charges).
* **Validation** **[paper]**. Poincare for SU(N): a manifold homotopy equivalent to SU(N) is SU(N) for N <= 3 (published for SU(3)
  **[external]**; for N >= 4 it fails, by a surgery computation here; for odd N the surgery obstruction in L = Z is still to be
  shown to vanish). Sp(2) is strongly rigid, by a surgery computation, independently read; G2 has exactly two structures, and
  whether the second is G2 itself is open. In Lean, G2's rigidity is restated as a one-box test: G2 is rigid if its rigidity box
  shares the gate with a certified box, and that sharing is a named hypothesis at least as strong as the rigidity it concludes, so
  the one assumption does not decide it (A.5r).

What is not proved: no problem is solved here. Each card has one named open step in Lean; the further open items of each part are
listed in that part.

* *Yang-Mills:* O1, the open step for the box (in Lean `FineOneBox`; the number F_e - 2c > log mu_4 is a sufficient, heuristic route
  to it, IV.5.6). The lower edge (O2, a correlation that does not vanish) is a second statement, independent of O1 in the paper's own
  model and put in the one assumption by a reading; the continuum construction and every compact simple group (O3, O4) remain for
  the Clay statement.
* *GRH:* a proof of Weil positivity from the primes and the real place alone. For zeta and for Dirichlet L-functions it holds
  through the external proof: RH and GRH for Dirichlet L-functions were proved in Lean by others in November 2026 (the Riemann
  hypothesis certified by the Lean FRO and the Mathlib Initiative), by a route that, as far as this project traced it, does not go
  through Weil's positivity criterion **[external, traced]**. GRH beyond Dirichlet L-functions is open, and no card is written for
  it yet.
* *NP vs coNP:* the card's open step `CrossingCost`; the paper's route to it is lifting with constant-size gadgets for cutting
  planes on lifted formulas (`LiftCPConst`, open for suitable gadgets such as indexing, false for XOR), and with it super-polynomial
  lower bounds for cutting planes on lifted formulas. Interface hardness at width 3 (VI.4.10) is a further item; its relation to
  `LiftCPConst` is not stated in Lean.
* *Navier-Stokes:* regularity or blowup of the equations themselves (route I: `PeriodContraction`). DMP's reading takes blowup as the
  expected outcome (the equations are not DMP-complete); the reading was made after the posted claims, and global regularity would
  refute it. Two posted blowup claims by others are unrefereed and unchecked here; one rests on a certificate that is announced, not
  released.
* *BSD:* the rank equals the order of the zero at s = 1, over Q from order 2 on (over other number fields, in general).
* *Hodge:* codimension p >= 2 in general.
* *GU:* the checkable consequence taken for the gate is uniform charge quantisation, which any compact U(1) also gives; a consequence
  beyond it is open, and the hypercharges are an input.

The paper stays a draft until the assumption is proved: each open step is stated in the exact form that would close it, so that
closing one changes one row of the claims ledger, one verdict line and one item of this list.

### What a reader can take from it

* From **mathematical physics**: the Yang-Mills gap reduced, for SU(2), to one inequality for one box of fixed physical size, the
  box passing the test by restatement, with the rest of the mechanism machine-checked; the Navier-Stokes cards with the status of
  the posted blowup claims stated exactly.
* From **number theory**: the explicit formula for all zeros in Lean, the first box of Weil's positivity certified with its margin,
  and why that margin cannot be carried outward by computation; a Mathlib-only BSD core over number fields, in IM.
* From **algebraic geometry**: the Hodge index and Weil's bound as linear algebra in Lean from named inputs, and the Hodge-index
  route to the Riemann hypothesis over finite fields read as the more efficiently correct one for this structure, beside Deligne's
  complete proof.
* From **topology**: Poincare for SU(N) argued in prose (rigid exactly for N <= 3; SU(3) from the literature), Sp(2) strongly rigid
  (a surgery computation, independently read), and the structure set of G2 counted (not machine-checked).
* From **complexity theory**: the crossing theorem for every two-premise proof system on expanding, minimally unsatisfiable
  formulas, and the open step of NP vs coNP reduced to one lifting statement for cutting planes.
* From **logic and verification**: a machine in which every open part is a named hypothesis, every axiom shows in the kernel's
  report, and a lint and a second kernel check every change; undecidability and the floor as the two sides of one test.

### A guide by ear: the tempered piano

This guide is not part of any argument. It is offered as a picture to hold while reading, and the idea of hearing existence through
tuning came to the first author from a short published by Vsauce; it is credited here, under that name, for that transfer.

* **Tuning is built from 2 and 3.** The octave is the ratio 2, the fifth the ratio 3/2. Pitch, taken modulo the octave, is a circle,
  and a fifth is a rotation on it **[classical]**.
* **The rotation does not close by itself.** Because log2(3) is irrational, twelve pure fifths overshoot seven octaves by the
  Pythagorean comma, 3^12 / 2^19 = 1.01364 **[classical]**. This is the finite loss at the start that the paper excises: the first
  box at {infinity, 2, 3} (Part V) is where the two generators of the tuning meet.
* **Temperament is the balanced state.** Equal temperament spreads the comma evenly over all twelve steps (each fifth becomes
  2^(7/12)), so the rotation closes and every key is equivalent; twelve is not arbitrary, since 19/12 is a convergent of log2(3)
  **[classical]**. In the paper's words, the rotation gives the tuning a direction and makes every tick alike (Part III, the tick
  operator) **[reading]**.
* **The zeros are the strings.** The explicit formula (Part V) writes the primes as a sum of tones: each nontrivial zero
  1/2 + i gamma sounds at frequency gamma in log x. On the critical line every tone has the same amplitude, x^(1/2); the Riemann
  hypothesis says that every string is tuned to the same loudness **[classical]**.

The guide ends where the tuning does: on the final tone, resonating outward. Nothing more is stated about it than that such a
configuration is describable, and that in that description it is DMP-complete **[reading]**.

### How to read the status marks

Every statement carries one of nine marks. **[Lean]**: machine-checked here, standard axioms only, module named. **[classical]**:
known, with a reference. **[external]**: a result by others, read but not rebuilt. **[conditional]**: under a named assumption.
**[paper]**: argued here in prose. **[numerical]**: measured here; it can refute, never prove a for-all statement. **[certified]**:
enclosed in ball arithmetic, with its log. **[reading]**: a DMP interpretation, never mathematics. **[open]**: not settled.

A mark may carry a qualifier after a comma or semicolon. "from X" names the inputs a Lean result rests on (named hypotheses,
`External` slots, a classical theorem taken as input). "recalled": stated from the literature without its page being read for this
draft. "traced": the project followed the external work's route itself, in part. "unverified": an external claim not checked here,
"certificate unreleased" when its certificate is announced but not public. "an estimate": a prose estimate, not a proof. "re-checked":
also passed by a second kernel. **[sketch]** and **[unchecked]** are **[paper]** arguments not yet read by a second person. "open in
general", "open where marked": the mark holds for the cases named, the rest is open. The claims ledger (`../CLAIMS.md`) lists every
claim with its mark, source and what would upgrade it.

### The three verification layers

The work behind this paper is checked three ways: by proof (on paper and in Lean), by the literature, and by computation. The
computations can refute a statement or guide a proof; they never establish a statement about all cases. Every measured number in the
paper is tied to the statement it would discharge, and a passing measurement is reported as consistent, not as proof. The Lean is
re-checked by independent kernels (Part II, II.7, with the commit of the last run), and IM's arsenal passes its lint at every change,
listing every part left open by name.

### What is new

* The machine as one object: running systems, their ledger, the encoder, and the settle theorem with its edge, decidable within an
  explicit bound under a cost floor and undecidable for the universal machine at no floor **[Lean]**.
* The one-box test: one command at one shared gate, a marker per step; the one-box and scale certificates; O1 restated exactly as
  DMP-completeness of the Yang-Mills box (chain form, by construction); rigidity as a one-box test **[Lean]**.
* The form layer as one API: every problem a card with one named open slot, and R136a1 (in IM's arsenal) as the named answer
  "outside" **[Lean]**.
* The explicit formula for all nontrivial zeros of zeta by the contour shift, on a Mathlib-only core **[Lean]**, and the first box of
  Weil's positivity with the primes 2 and 3 and explicit margins **[certified]** for the enclosures, **[paper]** for the estimates.
* The hand-over bound, the strict twist bound for every SU(N), and zero join loss in slab form **[Lean]**.
* A Mathlib-only BSD core over number fields, published in IM **[Lean]**.
* One geometry, two edges: GRH and O1 proved to ask opposite, independent bounds of one distance **[Lean]**.
* Poincare for SU(N), Sp(2) strongly rigid, and G2's two structures, by surgery from classical theorems **[paper]**, with SU(3) from
  the literature **[external]**.

What is *not* new is listed with references at each use: Osterwalder-Schrader, Weil, Hodge-Riemann, Lefschetz, Deligne, Dobrushin,
Lee-Yang, Pringsheim and Landau, Mordell-Weil, Hasse, Gross-Zagier-Kolyvagin, Cook-Reckhow, the barrier theorems, Perelman, the
surgery theory of Browder, Novikov, Sullivan, Wall and Kirby-Siebenmann, and, for Weil positivity at small support, Yoshida and
Connes-Consani.

### Plan

Part I: DMP, the vocabulary. Part II: the machine, then the tools the problems use. Part III: the one assumption and the rigid start.
Parts IV to X: the seven problems, one template each (Yang-Mills, GRH, P vs NP, Navier-Stokes, BSD, Hodge, GU). Part XI: Outlook.
Appendix A: validation (Poincare, SU(N) and the rigid groups).
