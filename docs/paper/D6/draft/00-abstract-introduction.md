# Grand Unified Information Duality v8: The Millennium Prize Problem type as seen through DMP, with certified settling

*Draft 6, machine-first. Not a claim of a solution of any Millennium Prize problem: the results that need the one assumption (Part
X) are conditional on it. Claim labels (0.n) are listed in `../CLAIMS.md`.*

## Personal note by the first author

In v1 I invited everyone to use their own intuition to make the derivations which I could see slumbering inside, but which I did not
feel worthy of waking myself. Since no one had any interest in that, I finally got frustrated by it and, after GRH got proven and
certified, I decided to take a look if Yang-Mills is something where I could finally get a nice verification that can't be ignored,
since I previously presumed that DMP also gives YM. One thing led to three, since those three are one, so the initial goal of one
Millennium Problem attempt turned into three, which revealed the MP-type, and let me generalize while sharing the credit with those
that phrased the correct problem :D

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

Each problem is restated as one statement checked at every step of a sequence. The restatement holds exactly when the problem's statement holds at every step,
so a proof has one shape, an induction: a base case and an inductive step. Once both are shown it holds at every step, and at every scale related by a map that keeps the step and the check. On binary data, read as real numbers,
every computation can be made reversible, so complex mathematics applies exactly. Six Clay problems are read this way, two in a
neighbouring form (GRH for the Riemann hypothesis, NP versus coNP for P versus NP), with a Grand Unified reading, not a Clay problem. The restatements are in Lean 4 with Mathlib, standard axioms only; DMP's readings are marked. Draft 6 adds DMP's explanation mechanism, a k by k table of which part proves which; a part costs 2k + 1 cells; derivation explains, never proves (Lean).

No problem is solved: on the cards the open problem is the base case, on the Yang-Mills box the inductive step between lattice levels (O1). One assumption is stated once, as a reading: the base cases of the cards of Yang-Mills, GRH, NP versus coNP, BSD and Hodge, each a different open statement; results using it are marked conditional. Proved in Lean
without it: the reduction of the SU(2) lattice mass gap to one named criterion on one box of fixed physical size, uniform in
spacing and volume; the explicit formula for all nontrivial zeros of zeta (its real-place term not yet matched to Weil's); a
crossing theorem for sound two-premise proof systems on expanding formulas; Mathlib-only cores for BSD and the Hodge index; the
full turn, giving the SU(N) hand-over log(1 + sqrt N) (electric sectors assumed positive, N >= 3) and the analytic rank as a
winding number. Weil's positivity on a first box, with the real place and the primes 2, 3, is enclosed in ball arithmetic, given analytic estimates argued in a note.

---

## Introduction

### What Draft 6 adds

Draft 6 grows from Draft 5 and adds one mechanism, which explains what Draft 5 establishes and claims nothing beyond it. A system is
k parts, and a k by k table says for each pair whether the row proves the column. The first author takes this table as DMP's
explanation mechanism **[reading]** (II.0.2). Exactly, in Lean on the kernel alone: a part is added by its own row, column and cell,
2k + 1 cells, and nothing already proven is checked again; derivation, the row proving a part that proves the column, always carries
its chain and on an all-`+` table changes nothing, so it explains and never proves; where the row does not use the column the cell
reflects positively, and where every use points to an earlier part no chain of uses returns **[Lean]** (II.0.2). Appendix E applies it
to what Draft 5 measured: the versions of DMP, Gravity and IM form such a DAG, every use proven; the two kernels accept every target;
a result of Draft 5 is explained by its chain; and the one open step O1 is a cell no derivation turns into `+` (E.6).

### What this paper is

This is a paper about one machine and one test, used seven times. The form under them is old: **positivity is existence**. A
positive weight makes a measure; a positive form makes a Hilbert space; a positive operator has its spectrum where it can be seen.
Osterwalder and Schrader reconstructed quantum field theories from reflection positivity. Weil reduced the Riemann hypothesis to the positivity
of one pairing. Hodge and Riemann found the same positivity on the cohomology of a variety, and Weil used it to prove the Riemann
hypothesis for curves over finite fields. Dobrushin showed that a contraction of local influences forces a unique equilibrium, and later work showed it is reached fast.

What is new is the shape put around it, in one statement in familiar terms. Each problem is restated as one statement checked at
every step of a sequence, and the restatement holds exactly when the problem's statement holds at every step. A proof then has one
shape, an induction: a base case and an inductive step. Once both are shown the statement holds at every step and, where scales are
related by a map that keeps the step and the check, at every scale **[Lean]** (II.4.1, IM's `Arsenal.Observable`). In DMP's words
the restatement is a *one-box description* of an *observable system*, *DMP-complete* exactly when the claim holds at every tick. The
restatement proves nothing by itself; the content is in the base case or in the inductive step, and the paper shows which. On a
problem card the statement checked is the same at every step, so the inductive step is free and the base case is the whole open
problem; on the boxes with a gate factor of their own (Yang-Mills, III.12; the model Navier-Stokes box, VI.8) the inductive step
carries the content. On binary data, read as real numbers, every computation can be made reversible by keeping its history, so
complex mathematics, the full turn of II.2.7 included, applies exactly **[classical]** (Bennett 1973; Toffoli 1980). The machine and
the test of the next section carry it. When every
step pays a cost above the floor,
settling is decidable within an explicit bound; when steps may pay exactly the floor, there are systems, the universal machine among
them, for which no procedure decides it. Each open step is restated as a box. One certifiable step is the same on every card: a
marker correct at the start and kept by the step is correct at every tick (the one-box certificate). On five cards the paper reads
the open step as one statement, that the card's box is DMP-complete, its gate shared at every scale **[reading]**; mathematically
each is a different statement, and the paper assumes it once (Part X). Navier-Stokes has no box of its own card under test: a model
box built from the energy bound alone gives a wrong marker. The Grand Unified card's open step lies outside its box. The paper proves
the machine and each card's core.

### The test in one page

Every result below uses these words in exactly these senses. Their Lean definitions are in II.3 to II.5; the DMP words not listed
here (ledger, floor, DB, G0, ODP) are in the table of I.8.

* **Running system** (II.3). States, a step from state to state, a factor in [0, 1] at each state, a mass >= 0 and a floor delta,
  with the ledger law mass(step x) <= e^delta fac(x) mass(x). A step *pays a cost above the floor* when e^delta fac(x) <= theta < 1
  for one theta and every state (the contraction class).
* **Box** (II.4, IM's `Arsenal.Rotation.Box`). A running system with a margin theta and a *marker* at every state, either *inside*
  or *R136a1* (outside). The *gate* reads inside at x exactly when fac(x) <= theta. A *tick* is one step. The marker at x is
  *correct* when it agrees with the gate. The box is **DMP-complete** from x0 when the marker is correct at every tick of the run from
  x0. This is the only meaning of "DMP-complete" in the paper's results; the first author's reading of it, that an object *runs on
  DMP*, is called *running* (X.4.4).
* **The one-box certificate** (`onebox_certificate`). If the marker is correct at the start and the step keeps it correct at every
  state, the box is DMP-complete. This is the certifiable step.
* **Restatement and induction** (II.4.1, IM's `Arsenal.Observable`). A system with states, one step and its own claim at each
  state (an *observable system*). Its restatement (the *one-box description*) is DMP-complete exactly when the claim holds at every
  step (`box_complete_iff`). A proof is an induction: the base case, the claim at the start, and the inductive step, a step that keeps
  the claim (`route`); then the claim holds at every step and, along a map of scales that keeps the step, the check and the marker,
  at every scale (`route_everywhere`). One failing step refutes it (`refuted_by_tick`). The cards below are such systems
  (`tickBox_observable`).
* **Card** (II.5, `API.Problem`). An input, one named open slot, a conclusion, and a Lean proof that the slot gives the conclusion.
  Its box (`cardBox`) is the constant box of the open statement: the ticks are 0, 1, 2, ..., the gate reads inside exactly when the
  open statement holds, and the marker is always inside, so the box is DMP-complete exactly when the open statement holds
  (`cardBox_complete_iff`). That is a restatement and proves no new bound. Only two boxes have a gate factor of their own: the
  Yang-Mills box (gate factor the best one-box ratio at each lattice level, III.12) and the model Navier-Stokes box (the energy bound against
  the viscous cost, VI.8).
* **Open parts.** A statement left open is a named hypothesis, never a Lean axiom: `OpenStep` and `External` in this repository,
  `R136a1` in IM's arsenal. The kernel's axiom report therefore lists only Lean's three standard axioms.
* **O1.** The Yang-Mills open step, in its Lean form `FineOneBox` (III.5.9): there are a cell geometry and constants such that at
  every lattice level and volume one box of fixed physical size has influence bounds, under every frozen boundary condition, whose
  one-box sum is below one. Its chain form `YMOneBox`, the path-counting number F_e(L) - 2C > log mu_4 and the hand-over side are
  routes to it, each related to it in III.5; where the paper means one of them, it names it.
* **The one assumption** (X.4.4). Its instances are each card's open slot and the sharing of a box's gate across scales; every
  result that uses it carries the mark **[conditional]**.

### Results and open steps

The results, by the problem they serve. Every Lean result names its module in the part that states it; "from X" names the inputs
it rests on.

* **The machine** **[Lean]**. The ledger, the encoder and its half-turn, the full turn (discrete and on a circle: coefficients,
  the factorial as one turn, the order of a zero as a winding number, and its balance log(1 + sqrt N), in IM's arsenal), the transport theorem, the settle theorem and its undecidable
  edge (for the universal machine, over all content), the one-box test with its one-box and scale certificates, and the card API.
  The one-box certificate needs a marker correct at the start and kept by the step at every state. In IM's arsenal, R136a1 is the
  one way to leave a statement open, a named hypothesis that never becomes an axiom; this repository's cards use the same
  transparent form under the names `OpenStep` and `External`.
* **Yang-Mills** **[Lean]**, for SU(2) on the lattice: reflection positivity, the strict bound between a sector and its twist (for
  every SU(N)), a per-box hand-over rate of at least log(1 + sqrt 2) (for the SU(N) twisted Wilson partition functions with no hypothesis on Z_tw, for beta != 0, even time extent and a
  nontrivial sector, `sun_handover`; over all N centre sectors by the full turn, log(1 + sqrt N), given positive electric sectors for N >= 3,
  `sun_handover_full_turn`; for the `Flip` object of SU(2) from positivity of its twisted partition function, a stated hypothesis), zero join loss in slab form, and the assembly from a one-box gap certificate to exponential decay of slab
  correlations (a lattice mass gap) in both orders of limits; the step to a gap of the Hamiltonian is argued in prose (III.2.7). The
  open step in the form the assembly uses is `FineOneBox`; the Yang-Mills card's own slot is the chain form `YMOneBox`, related to
  `FineOneBox` in prose (III.5.9). The box test restates both: each holds exactly when its box is DMP-complete (III.12; restatements
  by construction, no new bound).
* **GRH.** The explicit formula for all nontrivial zeros of zeta, classical (Weil 1952) and here formalised by the contour shift;
  its real-place term is a line integral at Re s = c > 1, whose identification with the term of Weil's closed form is not in Lean
  **[Lean]**. Weil's form positive with an
  explicit margin on the first box, where only the real place and the primes 2 and 3 enter: **[certified]** for the enclosures in
  ball arithmetic, **[paper]** for the analytic estimates that tie them to Weil's form (a working note, not independently read).
  Connes and Consani proved Weil positivity for test functions supported so close to 1 that only the real place enters, after
  Yoshida's work on the same Hermitian forms **[external, recalled]**; the first box here is the next range, with the primes 2 and 3
  and explicit margins. The positivity mechanisms in finite models **[Lean]**.
* **NP vs coNP** **[Lean]**. The crossing theorem for every sound two-premise proof system (the Ben-Sasson-Wigderson measure
  argument, machine-checked for every such system): on minimally unsatisfiable CNF formulas whose clause-variable graph expands,
  every refutation has a line sensitive to many variables (II.14, V.4); and the equivalence of the lifting interface with lifting by
  constant-size gadgets (V.4.11).
* **Navier-Stokes.** Three cards on the form layer; there is no Navier-Stokes object in the Lean, and Fefferman's forms (A) and (B)
  are named, not defined. A model box built from the energy bound alone gives the wrong marker at some scale, so that box is not DMP-complete (VI.8)
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
  **[external]**); for even N >= 4 it fails, by a surgery computation here; for odd N >= 5 the surgery obstruction in L = Z is still
  to be shown to vanish, so that case is **[open]**. Sp(2) is strongly rigid, by a surgery computation, independently read; G2 has exactly two structures, and
  whether the second is G2 itself is open. In Lean, G2's rigidity is restated as a one-box test: G2 is rigid if its rigidity box
  shares the gate with a certified box, and that sharing is a named hypothesis at least as strong as the rigidity it concludes, so
  the one assumption does not decide it (A.5r).

What is not proved: no problem is solved here. Each card has one named open step in Lean; the further open items of each part are
listed in that part.

* *Yang-Mills:* O1, the open step for the box (in Lean `FineOneBox`; the number F_e - 2c > log mu_4 is a sufficient, heuristic route
  to it, III.5.6). The lower edge (O2, a correlation that does not vanish) is a second statement, independent of O1 in the paper's own
  model and put in the one assumption by a reading; the continuum construction and every compact simple group (O3, O4) remain for
  the Clay statement.
* *GRH:* a proof of Weil positivity from the primes and the real place alone. For zeta and for Dirichlet L-functions it holds
  through the external proof: RH and GRH for Dirichlet L-functions were proved in Lean by others in November 2026 (the Riemann
  hypothesis certified by the Lean FRO and the Mathlib Initiative), by a route that, as far as this project traced it, does not go
  through Weil's positivity criterion **[external, traced]**. GRH beyond Dirichlet L-functions is open, and no card is written for
  it yet.
* *NP vs coNP:* the card's open step `CrossingCost`; the paper's route to it is lifting with constant-size gadgets for cutting
  planes on lifted formulas (`LiftCPConst`, open for suitable gadgets such as indexing, false for XOR), and with it super-polynomial
  lower bounds for cutting planes on lifted formulas. Interface hardness at width 3 (V.4.10) is a further item; its relation to
  `LiftCPConst` is not stated in Lean.
* *Navier-Stokes:* regularity or blowup of the equations themselves (route I: `PeriodContraction`). DMP's reading takes blowup as the
  expected outcome (the equations do not run); the reading was made after the posted claims, and global regularity would
  refute it. Two posted blowup claims by others are unrefereed and unchecked here; one rests on a certificate that is announced, not
  released.
* *BSD:* the rank equals the order of the zero at s = 1, over Q from order 2 on (over other number fields, in general).
* *Hodge:* codimension p >= 2 in general.
* *GU:* the checkable consequence taken for the gate is uniform charge quantisation, which any compact U(1) also gives; a consequence
  beyond it is open, and the hypercharges are an input.

This text is a draft in that sense: each open step is stated in the form whose proof would close its card, so that closing one
changes one row of the claims ledger, one verdict line and one item of this list. The project's release criterion (IX.0) lets the paper leave
the draft stage only when every open step is closed, so that both readings of its title hold.

### What a reader can take from it

* From **mathematical physics**: the Yang-Mills gap reduced, for SU(2), to one named criterion (`FineOneBox`) on one box of fixed
  physical size, restated exactly as the box test, with the rest of the mechanism machine-checked; the Navier-Stokes cards with the status of
  the posted blowup claims stated exactly.
* From **number theory**: the explicit formula for all zeros in Lean, the first box of Weil's positivity certified with its margin,
  and where this certificate stops (it failed at a = 0.75); a Mathlib-only BSD core over number fields, in IM.
* From **algebraic geometry**: the Hodge index and Weil's bound as linear algebra in Lean from named inputs, and the Hodge-index
  route to the Riemann hypothesis over finite fields read as the more efficiently correct one for this structure **[reading]**,
  beside Deligne's complete proof.
* From **topology**: Poincare for SU(N) argued in prose (rigid for N <= 3, SU(3) from the literature; not rigid for even N >= 4; odd N >= 5 open), Sp(2) strongly rigid
  (a surgery computation, independently read), and the structure set of G2 counted (not machine-checked).
* From **complexity theory**: the crossing theorem for every sound two-premise proof system on expanding CNF formulas, and the open step of NP vs coNP reduced to one lifting statement for cutting planes.
* From **logic and verification**: a machine in which every open part is a named hypothesis, every axiom shows in the kernel's
  report, and a lint and a second kernel check every change; undecidability and the floor as the two sides of one test.

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
configuration is describable, and that in that description it runs **[reading]**.

### How to read the status marks

Every result carries one of eleven marks: nine main marks and two for prose not yet read by a second person. **[Lean]**: machine-checked here, standard axioms only, module named. **[classical]**:
known, with a reference. **[external]**: a result by others, read but not rebuilt. **[conditional]**: under a named assumption.
**[paper]**: argued here in prose. **[numerical]**: measured here; it can refute, never prove a for-all statement. **[certified]**:
enclosed in ball arithmetic, with its log. **[reading]**: a DMP interpretation, never mathematics. **[open]**: not settled.

A mark may carry a qualifier after a comma or semicolon. "from X" names the inputs a Lean result rests on (named hypotheses,
`External` slots, a classical theorem taken as input). "recalled": stated from the literature without its page being read for this
draft. "traced": the project followed the external work's route itself, in part. "unverified": an external claim not checked here,
"certificate unreleased" when its certificate is announced but not public. "an estimate": a prose estimate, not a proof. "re-checked":
also passed by a second kernel. **[sketch]** and **[unchecked]** are **[paper]** arguments not yet read by a second person. "A + B" marks a statement with two
parts of two statuses (for example a Lean core with a classical input); "A / B" marks a statement whose status depends on the case
named beside it. "open in
general", "open where marked": the mark holds for the cases named, the rest is open. The claims ledger (`../CLAIMS.md`) lists every
claim with its mark, source and what would upgrade it.

### The three verification layers

The work behind this paper is checked three ways: by proof (on paper and in Lean), by the literature, and by computation. The
computations can refute a statement or guide a proof; they never establish a statement about all cases. Every measured number in the
paper is tied to the statement it would discharge, and a passing measurement is reported as consistent, not as proof. The Lean is
re-checked by independent kernels (Part II, II.7, with the commit of the last run), and IM's arsenal passes its lint at every change,
listing every part left open by name.

### Reproducing it

Every **[Lean]**, **[certified]** and **[numerical]** claim can be rerun from a clone of the repository with one script, stage by
stage: `tools/reproduce.sh paper D5` (the ledger and the PDF of this draft), `evidence` (the DMP evidence chain, "OK 285"), `lean` (the paper's
Lean against Mathlib, every axiom log compared line by line), `certs` (the certified first box, the three margins) and `kernels`
(the second kernels). `docs/paper/REPRODUCE.md` lists what each stage needs, how long it takes and what it prints when it passes;
the claims ledger `docs/paper/D5/CLAIMS.md` gives, for every claim, the declaration, log or reference that checks it. The repository is
https://github.com/StevenHrovat/gravity, at the commit printed on the title page, with this draft in `docs/paper/D5`
(Draft 4, which it grew from, stays unchanged in `docs/paper`); IM, whose arsenal the Lean imports at a pinned
commit, is https://github.com/StevenHrovat/im.

Two kinds of number appear in the text. Section numbers such as III.12 or X.4.4 name sections of this paper. Claim labels such as
X.64 or III.10c name rows of the claims ledger, which this PDF does not reproduce; in the PDF each claim label links to the ledger,
whose row gives the claim's status, its source and what would upgrade it. Where a number could be either, the text writes "claim".

### What is new

* The machine as one object: running systems, their ledger, the encoder, and the settle theorem with its edge, decidable within an
  explicit bound when every step pays a cost above the floor, and undecidable for the universal machine when steps may pay exactly
  the floor **[Lean]**.
* The one-box test: one command at one shared gate, a marker per step; the one-box and scale certificates; O1 restated exactly as
  DMP-completeness of the Yang-Mills box (chain form, by construction); rigidity as a one-box test **[Lean]**.
* The form layer as one API: every problem a card with one named open slot, and R136a1 (in IM's arsenal) as the named answer
  "outside" **[Lean]**.
* A Lean formalisation of the classical explicit formula for all nontrivial zeros of zeta, by the contour shift, on a Mathlib-only
  core **[Lean]**, and the first box of
  Weil's positivity with the primes 2 and 3 and explicit margins **[certified]** for the enclosures, **[paper]** for the estimates.
* The hand-over bound, the strict twist bound for every SU(N), and zero join loss in slab form **[Lean]**.
* A Mathlib-only BSD core over number fields, published in IM **[Lean]**.
* The headline as a theorem and an API: each problem restated as one statement checked at every step, exactly equivalent to it;
  a proof as an induction, base case and inductive step, holding at every step and, along a map of scales, at every scale (IM,
  `Arsenal.Observable`) **[Lean]**; on binary data read as real numbers every computation can be made reversible **[classical]**.
* The full turn as one tool, in IM's arsenal: it gives the hand-over over all N centre sectors, log(1 + sqrt N), also as a mean
  along a path, with positive electric sectors assumed for N >= 3, and reads the BSD leading coefficient and the analytic rank (a
  winding number) as one turn around s = 1 **[Lean]**; the encoder's half-turn is its case N = 2 **[paper]**.
* One geometry, two edges: a lower and an upper bound on one sequence of tick factors are independent and exclude each other on
  one sequence **[Lean]**; reading them as GRH's margin and O1 is the paper's identification **[paper]**; nothing is proved about GRH
  or O1 themselves.
* Poincare for SU(N) (even N), Sp(2) strongly rigid, and G2's two structures, by surgery from classical theorems **[paper]**, with SU(3) from
  the literature **[external]**.

What is *not* new is listed with references at each use: Osterwalder-Schrader, Weil (including the explicit formula), Hodge-Riemann, Lefschetz, Deligne, Dobrushin,
Lee-Yang, Pringsheim and Landau, Mordell-Weil, Hasse, Gross-Zagier-Kolyvagin, Cook-Reckhow, Ben-Sasson-Wigderson, the barrier theorems, Perelman, the
surgery theory of Browder, Novikov, Sullivan, Wall and Kirby-Siebenmann, and, for Weil positivity at small support, Yoshida and
Connes-Consani.

### Plan

Part I: DMP, the vocabulary. Part II: the machine, then the tools the problems use; its centre is II.4.1, the headline as a
theorem. Parts III to IX: the seven problems, one template each (Yang-Mills, GRH, P versus NP through NP versus coNP, Navier-Stokes,
BSD, Hodge, GU); each opens with the problem as a statement checked step by step, says whether its open part is the base case or the inductive
step, and ends at its card and its box. Part X: the one assumption, which on each card is its base case, and the rigid start, which
compares the cards once they have been read. Then the Outlook
(sections XI.n). Appendix A: validation (Poincare, SU(N) and the rigid groups). Appendix R: DMP's neighbours and the first author's
readings that no card uses. Appendix T: the verify toy, the headline run on binary words, to read in full and rerun.
