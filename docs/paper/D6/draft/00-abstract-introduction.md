# Grand Unified Information Duality v8: The Millennium Prize Problem type as seen through DMP, with certified settling

<!-- draft-subtitle: The ETM as the ODP running DMP in D6 -->
<!-- typeset: cited-bibliography, strict-periods -->
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
`balanceBound 1 (1/1000) (1/2) = 1001` steps at most (II.3) **[Lean]**, a general bound and a loose one here, where ten
halvings already suffice. On the circle itself nothing forces the run to settle, and for
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
gapless sequence has no ledger (`gapless_rejected`) and, as the simplest illustration, that assigning `+` and `-` settles nothing
(`assignment_does_not_decide`) **[Lean]**. A step that does not follow is not discarded: it is kept as a question, `?`, still posed and so still possible (R.12m). The first
author: this keeps DMP itself from accidentally becoming vacuous, so tight that it must always confine; that has been refuted
actively at every step, which is how it works **[reading]**. The exact part: a framework that can say no is not vacuous, and this one
does, on its own record: its optimizer finds the project's own versions not settled (E.9), the counting ledger rejects the
gapless sequence (`gapless_rejected`) **[Lean]**, and the matrix stage fails on any redundant use other than the one stated (E.9)
**[paper]**.

**How to read on.** Two routes lead on from here to the same conclusion, one through the exact results and one through the first
author's readings (after the throughline, next); every part also opens with a "Plug in here" note, so a reader who needs one part can start there.
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

### The first throughline: one step, v and c

The first author's newest readings, the two hands, the VIBE coefficient, its abstract statement, and c read as the circle (R.12m to
R.12q), are one picture, and the core page already holds it in miniature: three halvings around one full turn give 1/8. This section
lays the picture out once, each reading next to its exact part.

**The hands give the circle.** Two hands turning about a shared "up" turn independently, and the turns about one axis form the
circle (R.12m) **[classical]**. A mirror pair cannot be turned into each other; the sign -1 that separates them returns below as the
refutation.

**One step: a size and a turn.** Each step of the machine multiplies by a complex number: sizes multiply, angles add (II.0, C1)
**[classical]**. The first author names the two halves. The size is priced by the VIBE coefficient v, set to a = 0.69: v is log 2 to
two digits, the cost of one halving and one bit in natural units (C2) **[classical]**. The turn is c, read as the assertion that a
circle is classically circular, bent into the shape in which closure is inevitable and has not happened yet **[reading]** (R.12n,
R.12p). VIBE is DMP's word, defined before this paper was built: the VIBE field, mass times shortfall member by member, is an
expression, and its balance, the sum at zero, is an equation (DMP T32) **[paper]**; through the acronym the paper's terms get their
meaning, and any valid restatement of it is true **[reading]** (R.12n). The first author also reads v as the momentum that cancels in
E = mc^2; exactly, momentum cancels in the invariant E^2 - p^2 c^2 = m^2 c^4, and a rapidity of log 2, 0.69 to two digits, gives E : pc : mc^2 =
5 : 3 : 4 **[classical]** (R.12n).

**A run: closure is the next thing to happen.** Steps of a 1/N turn close exactly at the N-th: $e^{2\pi i k/N} \ne 1$ for
$0 < k < N$, and $e^{2\pi i k/N} = 1$ at $k = N$ **[classical]**. So closure is inevitable, has not happened at any earlier step, and
at step N - 1 is the next thing to happen (Figure 2). A turn that is no whole fraction of the circle never closes: twelve pure fifths
miss seven octaves because log2(3) is irrational, and tempering bends each fifth until the circle closes (claim 0.11)
**[classical]**. That bending is what the first author reads as c's assertion **[reading]**.

**At closure the value has no direction.** When the turns close, the angle drops out and the product is real: three steps of size 1/2
whose angles add to one full turn give 1/8, at a cost of 3 log 2 (the core page, point 2) **[classical]**. A positive value reads as
existence, `+` **[reading]**; one more half-turn, a multiplication by -1, makes it negative, and the negative is the refutation, as the
mirror is the other hand. A positive form behaves the same way: on its diagonal its value is real, so positivity is a sign anyone can
check. Reflection positivity for Yang-Mills and Weil's pairing for GRH are that sign, the first link of one chain (II.8); by Weil's
criterion one test function with a negative value would refute the Riemann hypothesis (II.9.4) **[classical]**, and up to the
support a = 0.69 no test function has one (IV.1) **[certified]** for the enclosures, **[paper]** for the analytic estimates.

**vAPIs: cards that assert their closure.** The first author reads the assertion of c as "vibe APIs", vAPIs: each claims that the
closure of its circle is the next thing to happen, and its refutation is defined by its negative **[reading]** (R.12p). Exactly, a card
states one claim with one open slot, a named hypothesis `R136a1`, never an axiom (II.5, II.6.2); its box checks the claim at every
step, viability, and carries it to every scale, universality; and one failing step refutes it (II.4.1, `refuted_by_tick`) **[Lean]**.

**The smallest element, and the notation.** The first author, most precisely: "Given certifiability literally minting the smallest
element of the set theory at DMP V0.9.9 at its containing root G0; and from there on always being able to assume
`"{inf,2,3}!"?"R136a1"`; and the open slot being a literal for the open set!" This is, in its entirety, DMP-complete, with the D6 tools
the 6D is asking for, and so within itself DMP-complete; which, when true, certifies the self-excisability of the box, certifying it
vibes. Made last, in a separate message, it is separated in time and meaning and given explicit directions, can be derived from the
facts of the statement, and becomes a live route as soon as anyone else agrees it is viable. It is written with six operators: `.` contains, `!` states, `?` asks, `;` a
decidability edge, `:` a commutative property, and `""` the empty set, the self-containing, DMP-complete G0 **[reading]** (R.12q).
Exactly: the smallest element of von Neumann's construction is the empty set, which is 0 (von Neumann 1923) **[classical]**. The
start {infinity, 2, 3} is certified up to the support a = 0.69 (X.58) **[certified]** for the enclosures, **[paper]** for the analytic estimates, and beyond it the open step stays a named
hypothesis, `R136a1`, never an axiom (II.6.2) **[Lean]**. Weil's form is taken on test functions supported in the open interval
(-a, a) (IV.1) **[classical]**. The decidability edge is II.3's: with a margin a run settles, on the circle it cannot be decided
**[Lean]**. Turns about one axis commute (R.12m) **[classical]**. The empty set is a subset of every set, itself included, and a
statement over no cases holds vacuously **[classical]**. A box whose claim fails at one tick is refuted by that tick, its own
excision (`refuted_by_tick`, II.4.1) **[Lean]**. In DMP a part acts only while both halves certify it (I.1) **[reading]**, so
agreement makes a route live; that it is viable in the Lean sense needs its base case and its step shown (`route`, II.4.1)
**[Lean]**. Care: in IM `P.NP` says that P is included in NP (R.10), so "contains" reads
it from the right; `!` marks a statement settled by a certificate anyone can check (I.8), of which "states" is the short form; the empty
set contains itself as a subset, never as an element, since it has no elements; and no consistent, effectively axiomatised system
strong enough for arithmetic proves its own consistency (Goedel 1931), so "DMP-complete within itself" is a reading, kept from being vacuous by
the refutations the paper proves (the core page, point 5).

**The abstract statement.** In the first author's words: the VIBE coefficient effectively allows the existence of all positively
constructable existence, as long as the rotation through its DB can be unified, by constructing a chain of causal arguments that
follows a valid direction in Real space, to result in reflection positivity as measured through the Riemann zeta, turning it into a
directionless value of the order Existence; thus certifying that any such constructed problem can be settled by the measurement of
its rotated refutation in Real space. The goal of this contraction: easier to understand, and simpler mathematics by asserting
existence explicitly, so that any valid possibility space can be built on any valid real space, read through a DMP-complete system
sharing root G0 **[reading]** (R.12o). Read along the steps above, each clause has its exact place: the chain is II.8's, the valid
direction is the one-way run of II.4.1, the directionless value is the real value at closure, the measurement is Weil's, the
refutation is the negative, and an asserted existence is a named hypothesis, visible in every statement that uses it **[Lean]** for
the form.

**Care.**

* The number and the circle are shared and the reasons differ: log 2 is a halving, a bit and, in GRH, half of log 4. Reading them as
  one throughline, and c as the circle, is the first author's. Since 1983 c is fixed by definition (R.12e), which is the exact sense
  in which it is asserted; c is a speed, not the circle's constant pi.
* Closure is inevitable only for a whole fraction of a turn; bending a step until it closes changes the step, a choice, not a proof.
* A refutation settles by one measurement, its absence does not: "any such problem can be settled" holds where a margin covers every
  case, as up to 0.69, and not in general (II.3, II.16).
* An asserted existence is assumed, and a result that uses it is conditional on it (R.12f).
* The name VIBE coefficient was first given to the fine-structure constant alpha, about 1/137; it now belongs to v (R.5b, R.12n).

Every part opens with a "Plug in here" note that says what it gives, what it needs, which route it belongs to and where v enters it
exactly, or that it does not; the two routes below follow v from stop to stop.

<!-- latex
\begin{figure}[ht]
\centering
\begin{tikzpicture}[x=1cm,y=1cm,every node/.style={font=\small}]
  \draw[gray!45] (0,0) circle (2.6);
  \foreach \k in {0,...,7} { \fill ({90-45*\k}:2.6) circle (2.2pt); \node at ({90-45*\k}:3.0) {\footnotesize $\k$}; }
  \foreach \k in {0,...,6} { \draw[->,thick] ({90-45*\k-6}:2.6) arc ({90-45*\k-6}:{90-45*(\k+1)+6}:2.6); }
  \draw[->,thick,dashed] ({90-45*7-6}:2.6) arc ({90-45*7-6}:{90-45*8+6}:2.6);
  \node[align=center,font=\footnotesize] at (0,0.75) {step $8$ closes: the product\\ is real, the turn drops out, $+$};
  \node[align=center,font=\footnotesize] at (0,-0.75) {one more half-turn, $\times(-1)$:\\ the negative, the refutation};
  \node[anchor=west,align=left,font=\footnotesize] at (3.5,1.3) {each step: size $\tfrac12$, cost $\log 2$\\ (the VIBE coefficient $v$, to two\\ digits), and a turn of $\tfrac18$ (the\\ circle, $c$ read as its assertion)};
  \node[anchor=west,align=left,font=\footnotesize] at (3.5,-1.5) {dashed: the closing step,\\ the next thing to happen\\ after step $7$};
\end{tikzpicture}
\caption{The first throughline as a picture. Eight steps of an eighth of a turn, each of size 1/2: before the eighth no step closes, and the
eighth does (dashed), so closure is inevitable and, until then, has not happened. At closure the product $2^{-8}$ is real and positive;
one more half-turn would make it negative, the refutation. The size is the first author's VIBE coefficient (log 2 per halving), the
turn the circle that the first author reads $c$ as asserting; the card that claims this closure as its next step is a vAPI.}
\end{figure}
-->

### The second throughline: reductio, from Moin to R136a1

The first throughline builds: a step, a run, closure, a positive value. The second refutes, and the first author reads it as the
mechanism that drives the whole: any believable reductio ad absurdum, running from Moin at the start to R136a1 at the finish, the
second throughline of existence, presented beside the first so that the two are truly dual **[reading]** (R.12r).

**Start: Moin.** Moin is the first author's label for a request that is proper while its satisfaction is open (R.9a)
**[reading]**. Exactly, it is the state of an IM channel between a verified accept and the established frame
(`ImChannelState.Moin`) **[paper]**, and every named open step of the paper is in that state: posed in plain words, taken only as a
hypothesis, never as an axiom (`OpenStep`, `R136a1`) **[Lean]** for the form. In binary Moin is the leading zero: rotating a word
left by one place doubles it exactly when its leading bit is 0 (`rotl_eq_double_iff`, R.9b) **[Lean]**.

**The mechanism: reductio ad absurdum.** Assume the negation of a claim, derive a contradiction, and the negation falls
**[classical]**. In the machine a claim stated for every step is refuted by one failing step (`refuted_by_tick`, II.4.1) **[Lean]**,
and in DMP a contradiction is excised, so that only "it does not exist" remains, refutation completeness (I.8) **[paper]**. The first
author: since the system is constructed in itself, it has to be attacked as the one box **[reading]**; exactly, the one-box test has
one shared gate, so a single failing tick anywhere refutes the claim of the whole (II.4) **[Lean]**. And the first author reads an
inverted assertion as the claim that a literal is a primitive, which is exactly what the attack looks for **[reading]**; exactly, a
literal is an atomic statement or its negation, and taking one as a primitive is taking it as an axiom, which the paper does for no
open step: the axiom logs (`docs/unified/*-axioms.log`) show only the standard axioms **[Lean]**, so every literal stays open to attack.

**Finish: R136a1.** R136a1 is the answer "outside": excision at transmission, after which only the remnant tail stays (I.8)
**[paper]**. In Lean it is the named hypothesis that never becomes an axiom, and its token holds exactly when its claim does
(`R136a1.iff`, II.6.2) **[Lean]**. What the attack leaves standing is what is named: a claim, with its open step a hypothesis visible
in every statement that uses it.

**Truly dual.**

| | The first throughline: construction | The second throughline: reductio |
|---|---|---|
| moves by | a step, a size and a turn (II.0) | an assumption and its contradiction |
| starts at | the base case (II.4.1) | Moin: the request proper, its satisfaction open (R.9a) |
| ends at | closure: a real, positive value, `+` | R136a1: what remains outside, named, not assumed (II.6.2) |
| a failure is | the negative, one more half-turn | a contradiction, one failing tick, excised |
| in Lean | `route` (II.4.1) | `refuted_by_tick` (II.4.1) |

Each claim of the paper is carried by the first throughline and attacked by the second: viability and universality build it, one
failing step refutes it, and what survives both is stated with its open step named **[Lean]** for the form (II.4.1).

**Care.**

* A reductio refutes only with a contradiction actually derived; "any believable" names the attempts, and a believed contradiction
  that is not derived refutes nothing.
* Refuting the negation gives the claim in classical logic, not in intuitionistic logic, where it gives only the double negation; the
  paper's Lean is classical, its axiom reports listing `propext`, `Quot.sound` and `Classical.choice` **[Lean]**.
* Moin and R136a1 as start and finish are the first author's reading. Exactly, both name one open step from two sides: posed, its
  satisfaction open, and held as a named hypothesis.
* One failing tick refutes the whole box, but which part failed still has to be found.

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
   a = 0.69 **[certified]** for the enclosures, **[paper]** for the analytic estimates; beyond it lies the open step.
5. **The cards together** (Part X): the one assumption as each card's base case, and the rigid start. *v*: the start
   {infinity, 2, 3} up to a = 0.69 (X.58), and remainders summed below log 2 deciding the sign step by step (X.7h) **[Lean]**.
6. **How the parts prove each other** (Appendix E, E.0.1 and E.0.2): the k by k table and the optimizer. *v*: does not enter.

Arriving: the headline holds as a theorem, a restatement that proves nothing by itself; each open part is named, and no open part is proved.

**Route 2, the reading route,** for a reader who starts from the first author's ideas. Each stop names the reading and the exact
part it stands next to; every reading is given in full in `READINGS.md`.

1. **The two hands** (Start here; R.12m): the vibe, two frames sharing an up and a down. Exact: orientation as the sign of a
   determinant **[classical]**.
2. **The two throughlines** (the sections before these routes; R.12n to R.12r): construction, one step of a size, v, and a turn, c,
   closing as the next step; and reductio, from Moin to R136a1, the negative as the refutation. Exact: log 2, one halving; a 1/N turn
   closing at the N-th step; Weil's criterion **[classical]**; one failing step refutes (`refuted_by_tick`) **[Lean]**.
3. **The vocabulary** (I.8): DMP's words, each with its plain meaning and its exact counterpart.
4. **The readings, each beside its exact part** (Appendix R, R.0): 0 = 1 in the zero ring (R.5a) **[Lean]**, the possibility space
   (R.11) **[Lean]**, the ETM as the ODP running DMP (R.12) **[Lean]** for the cycle of `r` and the one running system, and the
   rest, in one table.
5. **What does not follow, and why that is useful** (the core page, point 5). Exact: one failing step refutes (`refuted_by_tick`), and
   assigning `+` and `-` settles nothing (`assignment_does_not_decide`) **[Lean]**.

Arriving: every reading has met its exact part, and the conclusion is the one route 1 reached: the headline holds as a theorem, a restatement that proves nothing by itself;
each open part is named, and no open part is proved. The exact parts on the way differ (route 2 passes the zero ring, `r` and the running
system, which route 1 does not), and the table below joins them.

**Where the routes meet.** Each of the first author's names, its exact name, and where both stand; a reader can change routes at any
row.

| The first author's name | Exact name | Where |
|---|---|---|
| viability | induction: base case and inductive step (`route`) | II.4.1 |
| universality | a map of scales keeping the step, the check and the marker (`route_everywhere`) | II.4.1 |
| the VIBE coefficient v = 0.69 | log 2: one halving, one bit; GRH's certified support | II.0, IV.1, R.12n |
| c, the circle asserted circular | a 1/N turn closes at the N-th step and at no earlier one | II.0, R.12p |
| vAPIs, cards asserting closure next | a card's open slot, `R136a1`, a named hypothesis; refuted by one failing step | II.5, II.6, R.12p |
| `;`, a decidability edge | with a margin a run settles; on the circle it cannot be decided | II.3, R.12q |
| `:`, a commutative property | turns about one shared axis commute | R.12m, R.12q |
| `""`, the empty set, G0 | the empty set, 0 in von Neumann's construction, a subset of every set | R.12q |
| Moin, the start | an open step posed, its satisfaction open; an IM channel between a verified accept and the established frame | R.9a, R.12r |
| reductio, the second throughline | one failing step refutes a claim stated for every step (`refuted_by_tick`) | II.4.1, R.12r |
| the negative, the refutation | one negative value refutes a positivity claim (Weil's criterion) | II.9.4, R.12o |
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

### The contraction, and where the full text is

This is Draft 6 contracted, at the first author's request, so that it is short to read. Nothing proved left the record. Every claim
keeps its row, status and evidence in the ledger, `CLAIMS.md` (753 counted rows). The full Draft 6, with every derivation, is the git tag
`d6-full`, and Draft 5 holds the same derivations section by section. The first author's readings in full, clause by clause with their
exact parts and care points, are in `READINGS.md` beside this draft. The Lean that no claim, script or build reaches, the earlier
attempt rounds among it, left the build and stays at the tag. Each part keeps its "Plug in here" note, its statement as a check at
every step, what is proved, its card and its one open step, and ends with a pointer to its full text.

### Plan

Part I: the vocabulary (I.8). Part II: the machine: the ruleset (II.0), settling (II.3), the one-box test and the headline (II.4,
II.4.1), the cards (II.5), the chain of positivity (II.8), and what the tools do not do (II.16). Parts III to IX: the problems, each
with its card and its one open step. Part X: the one assumption. The Outlook: +AI and the applied idea of XI.4. Appendix A: validation
and the rigid groups, G2 among them. Appendix R: where the readings are, each beside its exact counterpart. Appendix T: the verify
toy. Appendix E: the explanation mechanism and the optimizer.
