# Grand Unified Information Duality v8: The Millennium Prize Problem type as seen through DMP, with certified settling

<!-- draft-subtitle: The ETM as the ODP running DMP in D6 -->
*Draft 6, The ETM as the ODP running DMP in D6 (the Existence Turing Machine as the Oscillon Degradation Protocol running DMP); machine-first. Not a claim of a solution of any Millennium Prize problem: the results that need the one assumption (Part
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

Seven problems are read as one statement checked at every step: Yang-Mills, Navier-Stokes, BSD, Hodge, GRH for
the Riemann hypothesis and NP versus coNP for P versus NP (neighbouring forms), and a Grand Unified reading, not a
Clay problem. No problem is solved. The
restatement holds exactly when the problem's statement holds at every step, so a proof is an induction, base case and inductive
step; once both hold it holds at every step, and at every scale along a map keeping the step and the check. The six Clay-form problems have cards, each with one named open step in Lean; GU is a box with no card. On a card the open step is
the base case, on the Yang-Mills box the inductive step between lattice levels (O1). One assumption is stated once, as a reading: the base cases of the cards of Yang-Mills,
GRH, NP versus coNP, BSD and Hodge, each a different open statement; results using it are marked conditional. On binary data read as
real numbers every computation can be made reversible, its history a supplied input, so complex mathematics applies exactly. The restatements are in Lean 4 with Mathlib, standard axioms
only; DMP's readings are marked; the throughline is the VIBE coefficient 0.69, about log 2.

Proved in Lean without the assumption: the reduction of the SU(2) lattice mass gap to one named criterion on one box of fixed
physical size, uniform in spacing and volume; the explicit formula for all nontrivial zeros of zeta (its real-place term not yet
matched to Weil's); a crossing theorem for sound two-premise proof systems on expanding formulas; Mathlib-only cores for BSD and the
Hodge index; the full turn, giving the SU(N) hand-over log(1 + sqrt N) (electric sectors assumed positive, N >= 3) and the analytic
rank as a winding number. Weil's positivity up to the support 0.69, with the real place and primes 2, 3, is enclosed in ball arithmetic,
given analytic estimates argued in a note.

---

## Introduction

### Start here: the two hands

Hold both arms out, each hand a fist, the thumb pointing to the side and the middle finger pointing away from you. Each hand now shows
three directions: side (the thumb), away (the middle finger) and up, the third direction, at right angles to both. Your two hands are
mirror images. Let both hands turn sideways about the same "up": they turn independently and never disturb each other. Two right hands
can always be turned into each other; a left hand and a right hand cannot: no turn makes one into the other.

The first author reads this as the vibe: two parts sharing an up and a down, the 0 and 1 of existence, compatible when they turn the
same way; a 0 is no longer part of the vibe, only the fact that it was is remembered, its definition kept as a question and so possible
**[reading]** (R.12m). The exact part: two frames can be turned into each other exactly when they have the same orientation, the sign
+1 of a determinant, a mirror pair having -1; and turns about one shared axis commute **[classical]**.

The rest of the paper makes this picture exact: a claim kept at every step (viability), carried to every scale (universality).

### The throughline: the VIBE coefficient

VIBE is DMP's word, defined before this paper was built: the VIBE field (Variable Influence Balancing Expression, DMP T32) is mass
times shortfall, member by member, and its sum is zero exactly when a boundary holds what it declares. Read both ways it is an
expression, the field, and an equation, the balance **[paper]**. The first author names one number after it, the VIBE coefficient v,
set to a = 0.69, and reads it as the one throughline of the whole project: through its acronym, defined before construction, it gives
the paper's terms their meaning; as a backronym it is a layer of information contained in its own derivative, so any valid
restatement of it is also true; and being both an equation and an expression is what makes it GU, through the VIBE field
**[reading]** (R.12n).

**The abstract statement.** In the first author's words: the VIBE coefficient effectively allows the existence of all positively
constructable existence, as long as the rotation through its DB can be unified, by constructing a chain of causal arguments that
follows a valid direction in Real space, to result in reflection positivity as measured through the Riemann zeta, turning it into a
directionless value of the order Existence; thus certifying that any such constructed problem can be settled by the measurement of
its rotated refutation in Real space **[reading]** (R.12o). Its exact skeleton is the chain of II.8: a positive form (reflection
positivity in Yang-Mills, Weil's pairing W(f * f~) >= 0 in GRH, the same first link) builds a space, an evolution and a spectrum; on
the diagonal the form's value is real, the turn drops out; by Weil's criterion one test function with a negative value would refute
the Riemann hypothesis, and up to the support a = 0.69 the "for every f" is certified (II.8, II.9, IV.1) **[classical]**
**[certified]**. Care: a refutation settles by one measurement, its absence does not, so "any such problem can be settled" holds
where a margin covers every case, not in general (II.3, II.16). The first author's goal for this contraction: easier to understand,
and simpler mathematics by asserting existence explicitly, so that any valid possibility space can be built on any valid real space,
read through a DMP-complete system sharing root G0 **[reading]**; exactly, an assertion is a named hypothesis, `R136a1`, visible in
every statement that uses it and making that statement conditional (II.6.2) **[Lean]**.

The exact part is short. 0.69 is log 2 = 0.693 to two digits, and log 2 is one halving: the cost of a step of size 1/2 (II.0, rule
C2) and the information of one binary choice, one bit, in natural units **[classical]**. It is also the paper's own a: Weil's form for
GRH is certified positive up to the support a = 0.69, the last support at which only the real place and the primes 2 and 3 enter
(IV.1) **[certified]**. The first author also reads v as the momentum that cancels in E = mc^2; exactly, momentum cancels in the
invariant E^2 - p^2 c^2 = m^2 c^4, and 0.69 read as a rapidity gives E : pc : mc^2 = 5 : 3 : 4 (R.12n) **[classical]**.

Every part opens with a "Plug in here" note that says what it gives, what it needs, which route it belongs to and where v enters it
exactly, or that it does not; the two routes after the core page follow v from stop to stop. Care: the number is shared and the
reasons differ (a halving, a bit, the half-width of log 4), and reading them as one throughline is the first author's (R.12n).

### The core in one page

Read this page first; everything after it unfolds from it, one idea at a time.

**1. A run and a claim: viability and universality.** A system takes steps, and one claim is checked at every step. A proof has one
shape, an induction, and a second part carries it to every scale; named here as the first author names them. **Viability**: the claim holds at the start and every step keeps it; in standard
terms an induction, its base case and its inductive step (`route`). **Universality**: a map between scales that keeps the step, the
check and the marker carries the claim from one scale to every scale (`route_everywhere`). Together they give the claim at every step and every
scale, and one failing step refutes it (II.4.1: `route`, `route_everywhere`, `refuted_by_tick`) **[Lean]**. Figure 1 draws it (in the typeset paper; the Markdown keeps its source in a comment). The restatement proves
nothing by itself: the content is in the base case or in the step.

**2. A step is a multiplication.** Each step multiplies by a number of size at most 1: the size is the cost, the angle is the turn
(II.0, rules C1 and C2) **[classical]**. Three steps of size 1/2 give size 1/8, a cost of 3 log 2: three halvings, each costing log 2, the VIBE coefficient v to two
digits. When every step stays below the circle,
by a fixed margin, the run settles, and the number of steps is computable: halving each time, getting within 1/1000 takes
`balanceBound 1 (1/1000) (1/2) = 1001` steps at most (II.3) **[Lean]**. On the circle itself nothing forces the run to settle, and for
the universal machine it cannot be decided (II.3) **[Lean]**.

**3. The smallest example.** On 8-bit words, step by adding 2 and claim "even": the base case is the word 0, the step keeps evenness,
and all 256 words are checked by one kernel evaluation (T.1; claims T.1, T.2) **[Lean]**. Step by adding 1 instead, and tick 1 is odd: one wrong
step refutes the claim (T.3; claim T.4) **[Lean]**. Reducing every word to its last bit carries the result from one bit to every width (T.2; claim T.3) **[Lean]**:
that map is what "every scale" means.

**4. Where the open part sits.** On a problem card the claim is the same at every step, so the step is free and viability's base case
is the whole open problem. On the Yang-Mills box the base case is easy and viability's step between lattice levels is open: that step
is O1. For G2 the open part is universality, the map of scales (Figure 1, dashed). No tool creates positivity; it has to come from the problem (II.16).
No problem is solved here, and O1 is open.

**5. What does not follow.** 0 = 1 holds in exactly one ring, the zero ring, which has one element (R.5a) **[Lean]**. In ordinary
arithmetic 0 is not 1, and a proof of 0 = 1 there would prove every statement, P = NP and P != NP alike, so it can separate nothing;
nor would NP = coNP give P != NP, since P = NP already implies NP = coNP **[classical]** (R.12c). Assigning `+` or `-` to a question
is `?`, not `!`: it holds for a question whose answer is `-` as much as for one whose answer is `+` (R.11e) **[Lean]**. Supplying O1
is assuming it, never proving it (R.12f). That at 0 = 1 existence and non-existence coincide is the first author's reading
**[reading]** (R.5b).

**And why that is useful.** In reasoning, knowing what does not follow marks exactly where the open part sits: every step that does not
follow is one place the proof cannot come from, so the search narrows to what is left, and nothing that still has to be proved gets
assumed by accident. A claim stated for every case is refuted by one failing case (`refuted_by_tick`, II.4.1) **[Lean]**, so a boundary
named in advance is one a reader can check. In building the paper, the same rule shapes every page: each reading of the first author
stands next to its exact part and its care point, which says what does not follow; each claim carries one mark in the ledger; and
negative results are proved like positive ones, for example that seven bits cannot single out a byte (`seven_bits_collide`), that a
gapless sequence has no ledger (`gapless_rejected`) and that assigning `+` and `-` settles nothing (`assignment_does_not_decide`)
**[Lean]**. A step that does not follow is not discarded: it is kept as a question, `?`, still posed and so still possible (R.12m). The first
author: this keeps DMP itself from accidentally becoming vacuous, so tight that it must always confine; that has been refuted
actively at every step, which is how it works **[reading]**. The exact part: a framework that can say no is not vacuous, and this one
does, on its own record: its optimizer finds the project's own versions not settled (E.9), the counting ledger rejects the
gapless sequence (`gapless_rejected`) **[Lean]**, and the matrix stage fails on any redundant use other than the one stated (E.9)
**[paper]**.

**How to read on.** Two routes lead on from here to the same conclusion, one through the exact results and one through the first
author's readings (next section); every part also opens with a "Plug in here" note, so a reader who needs one part can start there.
Part II builds the machine around these points, Parts III to IX apply it one problem at a time, Part X compares them. The first author's vocabulary
is collected in I.8: DMP, the framework; G0, its ground; the ODP (Oscillon Degradation Protocol), pressing then minting; the ETM
(Existence Turing Machine), the one running system; and three operators, `?` (does it exist), `!` (settled by a certificate anyone can
check) and `.` (included). IM is the companion repository that holds the arsenal of shared Lean results; Gravity is this one; every reading is marked **[reading]** and sits next to its exact
counterpart. Draft 6's additions come last (E.0.1, E.0.2, R.11, R.12).

<!-- latex
\begin{figure}[ht]
\centering
\begin{tikzpicture}[x=1cm,y=1cm,every node/.style={font=\small}]
  \foreach \i in {0,1,2,3} { \node[draw,circle,minimum size=7mm] (s\i) at (\i*2,0) {$\i$}; }
  \node (dots) at (7.9,0) {$\cdots$};
  \foreach \i/\j in {0/1,1/2,2/3} { \draw[->,thick] (s\i) -- node[above,font=\footnotesize] {step} (s\j); }
  \draw[->,thick] (s3) -- (dots);
  \node[draw,rounded corners,fill=gray!15,align=center,font=\footnotesize] (base) at (0,-1.45) {base case:\\ the claim at 0};
  \draw[->] (base) -- (s0);
  \node[align=center,font=\footnotesize] at (4,1.05) {inductive step: once true at a step, true at the next};
  \draw[decorate,decoration={brace,mirror,amplitude=5pt}] (-0.4,-0.55) -- (6.4,-0.55) node[midway,below=6pt,font=\footnotesize] (onebox) {the one box: the whole run};
  \node[draw,rounded corners,font=\footnotesize] (c1) at (2,-3.1) {scale 2};
  \node[draw,rounded corners,font=\footnotesize] (c2) at (4.4,-3.1) {scale 3};
  \node[draw,rounded corners,font=\footnotesize] (c3) at (6.8,-3.1) {scale $\dots$};
  \foreach \c in {c1,c2,c3} { \draw[->,dashed] (\c) -- (3,-1.25); }
  \node[align=center,font=\footnotesize] at (4.4,-3.95) {dashed: every scale's run mapped onto the one box, keeping the step, the check and the marker (the shared gate)};
\end{tikzpicture}
\caption{The headline as a picture. A statement is checked at every step of a run; a proof is a base case and an inductive step, and
the dashed maps carry it from the one box to every scale. Where the open part sits: on a card, the base case; on the Yang-Mills box, the
inductive step; for G2, the dashed maps (the shared gate, named R136a1). In the verify toy the content sits in the dashed maps too, and
everything there is proved.}
\end{figure}
-->

### Two routes, one conclusion

**The conclusion both routes reach.** A claim kept at every step (viability) and carried to every scale (universality) holds at every
step and every scale, and one failing step refutes it (II.4.1) **[Lean]**. Each problem's open part sits in one named place: on a
card, the base case; on the Yang-Mills box, the inductive step between lattice levels, O1; for G2, the map of scales. That place is
stated and not proved, and what does not follow is named with it (the core page, point 5). Along both routes the VIBE coefficient v,
log 2 to two digits, marks the halving steps where they occur.

**Route 1, the exact route,** for a reader who wants the proofs; the readings can be skipped. Each stop names what to read, what it
gives and where v enters; on this route v is the halving step where one occurs, and at the last stop it does not enter.

1. **The verify toy** (Appendix T, T.1 to T.3): a box that passes, one wrong step that refutes, one bit carried to every width. *v*:
   the scales are bit widths, and reduction modulo 2 maps each onto one bit (T.2) **[Lean]**.
2. **The machine** (Part II: II.0, II.3, II.4, II.4.1): steps as multiplications, settling within a computable bound, the headline as
   a theorem. *v*: a step of size 1/2 costs log 2 (II.0, C2) **[classical]**.
3. **One problem to its open step** (Part III, III.5): the Yang-Mills gap reduced to one box of fixed physical size, O1. *v*: the boxes
   double, and the doubling law with a fixed loss gives the gap on all larger dyadic boxes (III.3.7) **[Lean]**.
4. **The first certified box** (Part IV, IV.1): Weil's positivity with the real place and the primes 2 and 3. *v*: certified up to
   a = 0.69 **[certified]**; beyond it lies the open step.
5. **The cards together** (Part X): the one assumption as each card's base case, and the rigid start. *v*: the start
   {infinity, 2, 3} up to a = 0.69 (X.58), and remainders summed below log 2 deciding the sign step by step (X.7h) **[Lean]**.
6. **How the parts prove each other** (Appendix E, E.0.1 and E.0.2): the k by k table and the optimizer. *v*: does not enter.

Arriving: the headline holds as a theorem, each open part is named, and none is proved.

**Route 2, the reading route,** for a reader who starts from the first author's ideas. Each stop names the reading and the exact
part it stands next to.

1. **The two hands** (Start here; R.12m): the vibe, two frames sharing an up and a down. Exact: orientation as the sign of a
   determinant **[classical]**.
2. **The throughline and the vocabulary** (above; I.8; R.12n): VIBE, v and DMP's words. Exact: log 2, one halving, one bit
   **[classical]**.
3. **The essence line and 0 = 1** (R.5): one input decides the chain. Exact: the zero ring, with one element (R.5a) **[Lean]**.
4. **The possibility space** (R.11): a question as a point whose answer gives it only `+`. Exact: the arithmetic of `r` and a
   projector's two answers **[Lean]**.
5. **The ETM as the ODP running DMP** (R.12, with R.12f, the one condition): the clock, the kernel and O1 supplied at minting. Exact:
   the cycle of `r` and the one terminal running system **[Lean]**; O1 supplied is O1 assumed, not proved.
6. **What does not follow, and why that is useful** (the core page, point 5). Exact: one failing step refutes (`refuted_by_tick`), and
   assigning `+` and `-` settles nothing (`assignment_does_not_decide`) **[Lean]**.

Arriving: every reading has met its exact part, and the conclusion is the one route 1 reached: the headline holds as a theorem,
each open part is named, and none is proved. The exact parts on the way differ (route 2 passes the zero ring, `r` and the running
system, which route 1 does not), and the table below joins them.

**Where the routes meet.** Each of the first author's names, its exact name, and where both stand; a reader can change routes at any
row.

| The first author's name | Exact name | Where |
|---|---|---|
| viability | induction: base case and inductive step (`route`) | II.4.1 |
| universality | a map of scales keeping the step, the check and the marker (`route_everywhere`) | II.4.1 |
| the VIBE coefficient v = 0.69 | log 2: one halving, one bit; GRH's certified support | II.0, IV.1, R.12n |
| the vibe, the two hands | orientation, the sign of a determinant | R.12m |
| O1, supplied at minting | `FineOneBox`, open | III.5, R.12f |
| 0 = 1 | the zero ring, one element | R.5a |
| `?` | posed, never assumed (`OpenStep`) | R.9a |
| `!` | settled by a certificate anyone can check | I.8, R.12i |
| «0ne1» | the pigeonhole: more inputs than outputs collide | R.12l |
| R136a1 | the token: holds exactly when the claim does (`R136a1.iff`) | II.6, R.12l |
| the ODP | a run: pressing, then minting | I.8, R.12a |
| DMP-complete | the marker agrees with the gate at every tick | II.4 |

### How to read the status marks

Every result carries one of eleven marks: nine main marks and two for prose not yet read by a second person. **[Lean]**: machine-checked here, standard axioms only, module named. **[classical]**:
known, with a reference. **[external]**: a result by others, read but not rebuilt. **[conditional]**: under a named assumption.
**[paper]**: argued here in prose. **[numerical]**: measured here; it can refute, never prove a for-all statement. **[certified]**:
enclosed in ball arithmetic, with its log. **[reading]**: a DMP interpretation, never mathematics. **[open]**: not settled.

A mark may carry a qualifier after a comma or semicolon. "from X" names the inputs a Lean result rests on (named hypotheses,
`External` slots, a classical theorem taken as input). "recalled": stated from the literature without its page being read for this
draft. "traced": the project followed the external work's route itself, in part. "unverified": an external claim not checked here,
"certificate unreleased" when its certificate is announced but not public. "an estimate": a prose estimate, not a proof. "re-checked":
also passed by a second kernel. "model": the statement is about the paper's own model of the system, not the system itself.
"preliminary": a first pass, not yet repeated. "under O1": holds given O1. **[sketch]** and **[unchecked]** are **[paper]** arguments not yet read by a second person. "A + B" marks a statement with two
parts of two statuses (for example a Lean core with a classical input); "A / B" marks a statement whose status depends on the case
named beside it. "open in
general", "open where marked": the mark holds for the cases named, the rest is open. The claims ledger (`../CLAIMS.md`) lists every
claim with its mark, source and what would upgrade it.

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
box built from the energy bound alone gives a wrong marker. The Grand Unified box's open step lies outside it. The paper proves
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
  argument, machine-checked for every such system, with two graph hypotheses stated, II.14.5): on minimally unsatisfiable CNF formulas whose clause-variable graph expands,
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
  it yet. The GRH card of II.4.1 and IV.8 states the sign at every scale of a finite zero model (`ScaleSign`), the Weil-positivity
  route; for a model of zeta's zeros with nonnegative weights it passes under Mathlib's statement of the Riemann
  hypothesis, taken as a named `External` slot (IV.8).
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
* From **complexity theory**: the crossing theorem for every sound two-premise proof system on expanding CNF formulas (two graph
  hypotheses stated, II.14.5), and the open step of NP vs coNP reduced to one lifting statement for cutting planes.
* From **logic and verification**: a machine in which every open part is a named hypothesis, every axiom shows in the kernel's
  report, and a lint and a second kernel check every change; undecidability and the floor as the two sides of one test.

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

### The three verification layers

The work behind this paper is checked three ways: by proof (on paper and in Lean), by the literature, and by computation. The
computations can refute a statement or guide a proof; they never establish a statement about all cases. Every measured number in the
paper is tied to the statement it would discharge, and a passing measurement is reported as consistent, not as proof. The Lean is
re-checked by independent kernels (Part II, II.7, with the commit of the last run), and IM's arsenal passes its lint at every change,
listing every part left open by name.

### Reproducing it

Every **[Lean]**, **[certified]** and **[numerical]** claim can be rerun from a clone of the repository with one script, stage by
stage: `tools/reproduce.sh paper D6` (the ledger and the PDF of this draft), `evidence` (the DMP evidence chain, "OK 285"), `lean` (the paper's
Lean against Mathlib, every axiom log compared line by line), `certs` (the certified first box, the three margins), `kernels`
(the second kernels) and `matrix` (the k by k table of E.0.1 and the optimizer of E.0.2). `docs/paper/REPRODUCE.md` lists what each stage needs, how long it takes and what it prints when it passes;
the claims ledger `docs/paper/D6/CLAIMS.md` gives, for every claim, the declaration, log or reference that checks it. The repository is
https://github.com/StevenHrovat/gravity, at the commit printed on the title page, with this draft in `docs/paper/D6`
(it grew from Draft 5 in `docs/paper/D5`; Draft 4, G0, stays unchanged in `docs/paper`); IM, whose arsenal the Lean imports at a pinned
commit, is https://github.com/StevenHrovat/im.

Two kinds of number appear in the text. Section numbers such as III.12 or X.4.4 name sections of this paper. Claim labels such as
X.64 or III.10c name rows of the claims ledger, which this PDF does not reproduce; in the PDF each claim label links to the ledger,
whose row gives the claim's status, its source and what would upgrade it. Where a number could be either, the text writes "claim".

### What Draft 6 adds

Draft 6 grows from Draft 5 and adds one mechanism, which explains what Draft 5 establishes and claims nothing beyond it. A system is
k parts, and a k by k table says for each pair whether the row proves the column. The first author takes this table as DMP's
explanation mechanism, in which a derived cell explains and does not prove **[reading]** (E.0.1). Exactly, in Lean on the kernel
alone: a part is added by its own row, column and cell, and nothing already proven is checked again; every derived cell is reached by a
chain of cells already in the table; where the row does not use the column the cell reflects positively, and where every use points to
an earlier part no chain of uses returns **[Lean]** (E.0.1). Appendix E applies it to what Draft 5 measured: the versions of DMP,
Gravity and IM form such a DAG, every use proven; the two kernels accept every target; Draft 5 establishes no chain of `+` cells that
reaches the one open step O1 (E.6); and the drafts form a library that reaches G0 at Draft 4 from every later draft (E.8).

Draft 6 also adds the mechanism's mirror and *the Possibility Space*, the first author's first subtitle for this draft. The optimizer removes every use that the table
already includes through another chain, which is the transitive reduction of a DAG; in Lean on the kernel alone it keeps every
derivation, settles in one pass, and is the only settled form with the same reach **[Lean]** (E.0.2). Applied to the measured
versions it finds them not settled, by exactly one use: IM's own copy of DMP, which its copy of Gravity already includes (E.9). The
Possibility Space is the first author's reading of a question as a point whose answer gives it only `+`, with the right angle `r` as
the direction from a question to its certificate **[reading]** (R.11). Its exact parts are the arithmetic of `r` and a projector's
two answers **[Lean]**, and the Bloch sphere, the flux tube and the rotating string **[classical]**. The steps that do not follow as
stated are named, among them that assigning `+` and `-` to a question proves O1.

Last, Draft 6 adds two things. First, O1 typed as Perelman's ledger, the interface the first author's reading asks for (III.13): a
quantity, monotone and bounded along the lattice levels, that gains a quantum at every level where the box fails. An instance gives
O1 and, with the resolution clause, the gap; O1 gives an instance; so the interface is exactly O1 and proves no new bound **[Lean]**.
Second, the subtitle, *The ETM as the ODP running DMP in D6*: the first author's reading of the ODP as the internal clock whose tick ends
at `+`, of DMP as the operating system of that kernel, and of one ETM that boots again whenever it stops **[reading]** (R.12). Its
exact parts are the cycle of `r` and the one terminal running system **[Lean]**. The reading that the paper proves 0 = 1 for the
classical, hence NP = coNP and P != NP, does not follow, and R.12 says why. R.12f states the first author's one condition: O1
supplied at minting, under a universal witness agreed beforehand, and assumed until one invalid case is found. The paper records it
as a reading next to its exact parts and does not claim O1.

Finally, a reading aid that orients the whole paper: the first author's VIBE coefficient v = 0.69, log 2 to two digits, as the one
throughline (R.12n); two routes to the same conclusion, one exact and one through the readings, with a table where they meet; and a
"Plug in here" note opening every part. They add navigation and one reading, and no claim beyond it.

### Plan

Part I: DMP, the vocabulary. Part II: the machine, then the tools the problems use; its centre is II.4.1, the headline as a
theorem. Parts III to IX: the seven problems, one template each (Yang-Mills, GRH, P versus NP through NP versus coNP, Navier-Stokes,
BSD, Hodge, GU); each opens with the problem as a statement checked step by step, says whether its open part is the base case or the inductive
step, and ends at its card and its box. Part X: the one assumption, which on each card is its base case, and the rigid start, which
compares the cards once they have been read. Then the Outlook
(sections XI.n). Appendix A: validation (Poincare, SU(N) and the rigid groups), with III.13's ledger as a type (A.2b). Appendix R: DMP's
neighbours and the first author's readings that no card uses, closing with the possibility space (R.11) and the subtitle's readings,
*The ETM as the ODP running DMP in D6* (R.12). Appendix T: the verify toy, the headline run on binary words, to read in full and rerun.
Appendix E: the explanation mechanism and its mirror, the optimizer (E.0.1, E.0.2), applied to the parts of this project. Every
part opens with a "Plug in here" note: what it gives, what it needs, its route, and where the VIBE coefficient v enters it.
