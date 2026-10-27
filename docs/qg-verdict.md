# Can DMP be assembled to model quantum gravity? The verdict

The owner, 2026-10-27 13:29Z: "Either: DMP CAN be assembled in a way that models what would be expected of Quantum Gravity; DMP CAN NOT
be assembled in a way that models what would be expected of Quantum Gravity; the problem can not be decided, in which case an honest
vibe is enough. As well as my accepting that conclusion."

This file answers that question for DMP 0.9.8 (`dmp` `45d3822`), read as written. It starts from Team Fable's cold read (gravity#22,
`docs/cold-read-physics.md`, sections 6 and 7) and does what that pass did not: it builds the strongest assembly, runs it, and only then
looks for the wall. The run is `docs/qg-verdict/assembly.py` (numpy only, a few minutes, 25 of 25 checks pass; checks [7] and [8] are the second pass, section 10). Nothing here changes
DMP. The owner judges.

## 0. The verdict

**Revised by the second pass (section 10, 2026-10-27 afternoon): CAN**, at the standard every published quantum-gravity model is held to
(X1 to X4 met; X5 open for DMP as for every discrete approach). Theorem A below stands as a theorem, but its conclusion "so X4 fails" does
not follow: gravity's quantum part can be content between parts, and Axiom 3's existence clause keeps every record blind to it (check
[7], Lean `blind_record_same`). What Theorem A finds is the area term of the quantum Ryu-Takayanagi formula (Harlow 2017), not a wall.
The first pass follows unchanged, so the step that was missing can be seen.

**First pass: CAN NOT.** Assembled as faithfully as it can be, DMP models a *classical* spacetime that carries *quantum* content: holography on a
fixed background (the level of the published holographic code models, on a tree the p-adic version of them) and gravity as an equation of
state (Jacobson 1995). It cannot model quantum gravity, because what makes gravity quantum, a geometry that can be in superposition and pass between two
masses **without being observed** (otherwise it cannot entangle them), is the one thing DMP's mission forbids: "absolute
Observability". Every structure DMP itself defines between parts (the layout, the trust field, the order of acts, the counts that drive
the layout) is held in full by two independent witnesses, and a thing two independent readers each hold in full is classical. Content
can still be entangled across parts (check [5]); but content is what DMP makes no statement about. A classical mediator cannot create
entanglement. That is two published theorems in a row
(section 4), and the run shows both ends of it (checks [5] and [6]).

The verdict is not "undecidable" because it does not depend on which physical quantity DMP's words are mapped to. Whatever DMP structure
is chosen to carry the geometry (the trust field, the layout, the causal order), DMP's own axioms make two witnesses hold it in full,
and that alone makes it classical. A mapping that puts the geometry in no DMP structure (inside a part, where DMP says nothing) does
not model gravity with DMP; it puts gravity in a box DMP never opens.

What the owner gains, honestly: Team Fable was right about where it ends and too strict about how far it goes. Three of its seven
conflicts, two of them called irremovable, dissolve in the assembly (section 3). And DMP takes a side that physics can test: it sits on
the classical-gravity side of the Galley-Giacomini-Selby no-go, with Jacobson and Oppenheim, and a positive tabletop result for
gravitationally mediated entanglement (Bose et al. 2017; Marletto and Vedral 2017) would refute that reading.

## 1. What "expected of quantum gravity" means here

Fixed before the assembly was built, so the target could not move to fit it. Five expectations, each from the mainstream literature:

| Id | Expected of quantum gravity | Source |
|---|---|---|
| X1 | Quantum content: superposition, correlations up to 2√2 | Cirel'son 1980; measured, Hensen et al. 2015 |
| X2 | Entropy of a region is the area of its minimal surface | Ryu and Takayanagi 2006 |
| X3 | The bulk is a quantum error-correcting code: a bulk point is recoverable from enough of the boundary | Almheiri, Dong and Harlow 2015; Pastawski, Yoshida, Harlow and Preskill 2015 |
| X4 | Gravity is quantum: the field can be in superposition and can entangle two masses | Donoghue 1994 (the low-energy theory of the metric is a quantum field theory, whatever completes it); test: Bose et al. 2017, Marletto and Vedral 2017; theorem: Galley, Giacomini and Selby 2022 |
| X5 | The classical limit is a Lorentzian 3+1 manifold obeying Einstein's equations | general relativity |

X5 is not reached by any published discrete model yet, so it cannot decide the question alone. X4 is the one that makes gravity
*quantum*; a model without it models something else.

## 2. The assembly, built and run

Each row is a DMP sentence, quoted from 0.9.8, and the object it becomes. The numbers in brackets are the checks in `assembly.py`.

| DMP, as written | The object | Check |
|---|---|---|
| "The part is defined as a Duality of Trust ... No further statements about its constituents" (G0) | One block of the five-qubit code (Laflamme et al. 1996): five physical qubits holding one logical qubit; its six-leg perfect tensor is the tile | [1] every three-leg cut carries 3 bits |
| "Every layer has its own Duality (T38) and is a tree rooted there" (Axiom 3) | A rooted tree of tiles: one root, five children, twenty boundary legs; each tile's bulk leg is the information that sits there | [2] both maps are isometries |
| "the fewest hops in total" (Axiom 3); "lowest total leakage" (the owner, level 0g of gravity#19) | The minimal cut through the tree; the entropy of every boundary region equals it (Ryu-Takayanagi on a tree) | [2] S(A) = min cut for every region tested |
| Majority within a type (the owner, 06:53Z, gravity#19 level 0c) | Entanglement wedge reconstruction: the root's information is recoverable from any 3 of the 5 children and from no 2 | [3] I = 2 bits for every triple, 0 for every pair |
| "two independent witnesses, each with full reach over the act" (Axiom 1); "verified itself at the point of use" (Axiom 2) | The trust half and the information half each read the stabilizer syndrome themselves; the gate passes only on two trivial syndromes | [4] both read the same syndrome on 200 random contents |
| "From trust nothing can be derived about information but its existence" (Axiom 3) | Stabilizers commute with the logical operators: the syndrome says the content is there and in the code, never what it is | [4] content fidelity 1 after both reads; [5] commutator 0 |
| "Where the two disagree, the stricter answer stands"; "what was lost without evidence against it, it restores by evidence" (Axiom 1) | A fault gives a nonzero syndrome, both halves refuse for the same reason, the correction restores the content | [4] 15 distinct syndromes; fidelity 1 after refuse and restore |
| "Content moves only by a grant" (Axiom 3) | Content is moved, never copied (no-cloning); if both halves read the content itself, half of it is lost | [4] fidelity 0.50 |
| T27: destroying the key destroys the item | Computational inaccessibility in a unitary world (Harlow and Hayden 2013): the bits are dispersed, not erased from physics | argued, section 3 |

Then the fork of gravity#19 ("isolated or entangled, never both") is not a fork inside one object but two layers of one assembly:

- **[5]** Two parts whose content is a logical Bell pair: the content reaches CHSH 2√2 = 2.828, while the two gates' verdicts sit at 2,
  the classical bound, at the same time. Gravity#17's `gate_obeys_chsh` and quantum content are both true; they are about different
  layers. The gate is classical by construction and does not need to be anything else.

So X1, X2 (on a tree) and X3 hold in an assembly that obeys all three axioms as written. This is as far as the published holographic
code models go.

## 3. What the assembly changes in Team Fable's cold read

Gravity#22 section 7 lists seven conflicts and calls three irremovable. The assembly shows that three of the seven came from the reading
chosen, not from DMP:

| Id | Cold read | In the assembly |
|---|---|---|
| Q2 (called irremovable) | "Two independent full readings of one quantum state do not exist" | True, and not needed. The halves read the syndrome, a commuting family, which can be broadcast (Barnum, Caves, Fuchs, Jozsa and Schumacher 1996: a family is broadcastable exactly when it commutes). Axiom 3 already restricts trust to existence. Dissolved without a change. |
| Q1 | A tree has no spacelike pair | True of the tree read as the causal order. Read as space (the bulk slice), siblings are spacelike and the tree is the bulk of p-adic AdS/CFT (Heydeman, Marcolli, Saberi and Stoica 2018; Gubser et al. 2017). Moved to section 4, theorem C. |
| Q7 (called irremovable) | Destruction on the legal date against unitarity | T27 destroys the key, not the bits; the content becomes computationally inaccessible inside the instance, which is how unitarity and inaccessibility coexist in physics (Harlow and Hayden 2013). Dissolved without a change. |
| Q3 (called irremovable) | DMP's geometry never acts on matter | Half dissolved: routing along the tree is geometry telling information where to go (geodesics); the layout following demand is matter telling geometry how to shape. What stays true is that geometry never enters the trust verdict, and general relativity does not ask it to. |

The other conflicts stand as Team Fable wrote them, and two of them are the wall in the next section.

## 4. The wall, by DMP's own words

**Theorem A. Every structure DMP defines between parts is classical.**

1. "Content moves only by a grant to a part trusted for its class" (Axiom 3). A move between two parts is therefore an act, with a
   definite source and destination. (The record names the act, not the content, so moved content can stay entangled, as in check [5].)
2. "Every grant, every use and every loss of trust leaves a record, written at the act, that every witness of that act can read in full"
   and "any other reader sees the counts always" (Axiom 3). The layout is "recomputed by both halves of the layer and never by one"
   (Axiom 3); every standing of the trust field is such a record (Axiom 2).
3. So every candidate for the geometry (the trust field, the layout, the order of acts, the demand that drives the layout) is held in
   full by at least two independent witnesses (Axiom 1).
4. A set of states that two parties can each hold in full is pairwise commuting (Barnum et al. 1996; for pure states, Wootters and
   Zurek 1982, Dieks 1982): no superposition of two layouts, two trust fields or two orders. Records that any number of readers see
   are classical in the strong sense (Brandão, Piani and Horodecki 2015).

In the assembly this is the statement that the area is a number, not an operator: DMP gives one fixed-area sector at a time, which in
real holography is a special state (Dong, Harlow and Marolf 2019), not the general one.

**Theorem B. A classical mediator cannot entangle.** If gravity entangles two systems and mediates their interaction locally, it is not
classical (Galley, Giacomini and Selby 2022, a theorem in generalised probabilistic theories; the experimental logic of Bose et al. 2017
and Marletto and Vedral 2017). Check [6] runs the smallest case: two masses in superposition coupled through a mediator. Coherent
mediator: negativity 0.5, entangled. The same mediator held by both halves, as Theorem A requires: negativity 0, separable.

**A and B together.** Any assembly in which a DMP structure is the geometry predicts that gravity never entangles two masses: X4 fails.
Any assembly in which no DMP structure is the geometry leaves gravity inside a part, about which G0 says "no further statements", so DMP
does not model it. There is no third place for the geometry to sit.

**Theorem C, separate and removable. The tree is not our space.** Read as space, a tree's boundary is totally disconnected (the
p-adic line of p-adic AdS/CFT, which is real and published) and no tree approximates a plane: an n-cycle needs distortion at least
n/3 − 1 in any tree (Rabinovich and Raz 1998). Read as the causal order, it has no spacelike pair (Team Fable,
`cr_ancestors_are_comparable`; Myrheim 1978). X5 fails under either reading of "every layer is a tree".

## 5. The three candidates, one line each

| Candidate | Still DMP as written? | What it models | Where it stops |
|---|---|---|---|
| Holographic codes (HaPPY, Ryu-Takayanagi, wedge reconstruction): parts as code blocks, trust as the syndrome | Yes, sections 2 and 3 | X1, X2 on a tree, X3 | X4 (A + B), X5 (C) |
| Causal sets: order as existence, count as information (gravity#19 level 0k) | No: needs a graph with several parents per line and random placement in place of the median layout (Bombelli, Lee, Meyer and Sorkin 1987), two changes to Axiom 3 | Discreteness, a clock as chain length | The order is held by both halves, so it is classical (A); quantum causal sets need a quantum measure over orders (Sorkin 1994), which A forbids |
| Jacobson's entanglement equilibrium (1995, 2016): the maintained median as the equilibrium | Yes in form (Axiom 1's balance and Axiom 3's median) | Einstein's equations as an equation of state | Needs a manifold (C) and a constant, 1/(4Għ), DMP does not have (cold read Q4); and Jacobson's own reading is classical: "it may be no more appropriate to quantize the Einstein equation than to quantize the wave equation for sound in air" |

All three land on the same side: classical geometry over quantum content.

## 6. What it would take to change the verdict, and whether that is minimal

To reach X4, the geometry must cross between parts without a record that both halves read. That needs two edits to Axiom 3:

1. The layout "recomputed by both halves" becomes "checked by both halves that it is a layout, never what it is", the same treatment
   Axiom 3 already gives every other piece of information. This is one clause and costs little.
2. The counts of the acts that shape the geometry (the demand) stop being something "any other reader sees ... always", and the acts
   stop being recorded where "every witness of that act can read [them] in full"; otherwise the source of the geometry is classical and
   so is the geometry it drives. This is not minimal: it is the mission sentence Axiom 3 carries, "while maintaining absolute
   Observability", and it is the reason two witnesses exist at all.

Edit 1 without edit 2 changes nothing: the demand that drives the layout is still a record, so the layout is still driven by a
classical source. Edit 2 is the price, and a DMP that pays it is no longer DMP. Theorem C is cheaper to remove (the hierarchy kept as
the routing tree of each request over a graph with loops), but removing it does not touch the wall.

## 7. For the paper

The sentence the evidence supports: *DMP's axioms force every quantity they share between parts to be classical; assembled as a
holographic code, they reproduce the minimal-cut entropy and majority reconstruction of the holographic code models on a fixed
background, and they place DMP on the classical side of the Galley-Giacomini-Selby no-go, the side of Jacobson's equation of state and
Oppenheim's classical gravity. A positive test of gravitationally mediated entanglement would refute this reading.* That is a
falsifiable stance, not a model of quantum gravity, and it is consistent with the framing the owner accepted at 08:09Z ("an
information-theoretic axiom system for trust, tested against quantum gravity").

## 8. The owner's reply: causality is the existence vector (2026-10-27 13:51Z)

Verbatim: "The arrow of causality is placed wrong. We placed the arrow along the scalar component of the Existence vector, when causality
actually IS the existence vector, finally given TRUE causality through the definition of causality as what was possible to happen in the
past, what can happen and what will happen, because everything that CAN happen, does happen. There is no causality without the decay
chain, as the initial decay is not an act, so would leave an orphaned causality root in it's stead."

**What holds.** "Everything that can happen does happen" is the relative-state reading of quantum mechanics (Everett 1957) and the sum
over histories (Feynman 1948): every possible history contributes. Read that way, Axiom 3's tree is neither space nor the causal order
but the tree of histories, each branch one consistent record (decoherent histories, Gell-Mann and Hartle 1990). That is a better reading
of the tree than either in theorem C, and it removes the cold read's Q1 objection (siblings are alternatives, not events that should be
spacelike). The initial decay as no act is G0's "stated, not derived" and gravity#19 level 0p; in the Lean the root's minting is
assumed (`cr_the_root_is_minted_by_assumption`), which is the orphaned root named correctly.

**What it does not move.** In the relative-state reading the two witnesses' records do not collapse anything; they become entangled with
the geometry, branch by branch. For the two masses that is the same thing: tracing out a record that carries which branch the mediator
took is exactly the dephasing of check [6], so the masses end separable in every branch and on average. Galley, Giacomini and Selby's
no-go is stated on the masses alone, so it does not care whether the record collapsed or branched. The only way back is to erase the
record coherently before the masses are compared, and Axiom 3 forbids that: the record "outlives the act" and is destroyed only by
both halves on the legal date. Inside each branch the tree is still a tree, so theorem C holds there unchanged.

**Effect on the verdict:** none. CAN NOT stands; the reply improves the reading of the tree and leaves theorems A and B where they were.

**The owner's follow-up (13:54Z), verbatim:** "This would be an issue only IF the very first guaranteed act, is the instant evaporation
of the perfect duality, because Existence has no beginning, without the definition of the PDs dualities end, as that IS minting."
Corrected 13:54Z: "Sorry, would not be, is actually correct." So the claim reads: the record is *not* an issue if the first guaranteed
act is the instant evaporation of the perfect duality, which is the minting.

Assessed: the premise is consistent and places quantum gravity exactly; the conclusion does not follow. Before the minting there is no act and so no record; an unrecorded geometry,
free to be in superposition, is allowed only there. The minting (the end of the perfect duality) is the first act, and from it on every
act leaves a record and theorems A and B apply. This matches the standard semiclassical picture in which the geometry of the universe
becomes classical through decoherence at its very beginning (Halliwell 1989; Kiefer 1987). The instant evaporation does not shorten the recorded era, it starts it: every act after the first, including every
laboratory test, leaves a record that outlives it, so the issue stands for every experiment that can be run. It does not change the
verdict: mainstream
quantum gravity still expects gravity to entangle two masses today (X4, the BMV test), and DMP says no. It names the second horn of
section 4 precisely: whatever is quantum about gravity lives before the minting, in G0, which DMP states and does not derive.

**The owner, 13:57Z, verbatim:** "The record of G0 Existence and the the part's linking to G0 can be proven axiomatically and actually
is. Something has to exist. If nothing exists, then it is before minting. Any causality before minting is logically undefinable, because
there is no before, we can only say what, in totality, can have the effects, that would be consistent with a G0 that produces an
Existances as close to ours as it can be, because Existance would not play hash collisions with itself, so all three WHK must be
irrational."

Assessed, sentence by sentence. *The linking is proven*: holds; every line descends from a minted root in the Lean, while the root's
minting itself is assumed by well-formedness (`cr_the_root_is_minted_by_assumption`), so "something exists" is still a candidate axiom
(gravity#19 level 0b), not a theorem. *No before the minting*: holds, and is the no-boundary proposal (Hartle and Hawking 1983, "no
before the Big Bang"); it confirms the second horn: what is quantum about gravity sits where DMP, by its own words, can say nothing.
*Only what is consistent with an existence like ours*: a selection principle, the weak anthropic form; it constrains, it does not
derive. *All three WKH irrational*: refuted for ħ, G and c, whose numbers are set by the choice of units (c is the exact integer
299 792 458 in metres per second since 1983, and all three are 1 in Planck units; Duff, Okun and Veneziano 2002); untestable for the
dimensionless constants, since no measurement of finite precision can show a number irrational; and irrational inputs do not prevent
collisions, which are a property of the map, not of its inputs (the digest's own collision, finding F7). **Effect on the verdict: none.**

**The owner, 14:00Z, verbatim:** "BUT: 2s1t is also theoretically possible still, right? So two whole numbers, in whatever number system
they may be (probably in relation to the quantum they define), can never be provable to either Exist or not, but never in between. A
binary Existance field with a spacetime obeying curvature, is just how our DMP turned out."

Read as two space dimensions and one time. Assessed: yes, possible, and it is where DMP fits best. Gravity in 2+1 dimensions has no
local degrees of freedom: no gravitational waves and no attraction between static masses, only conical deficits (Deser, Jackiw and
't Hooft 1984). It is an exactly soluble quantum theory, a Chern-Simons theory with two gauge factors whose two levels are the "two whole
numbers" (Witten 1988; Witten 2007 argues they are integers, with central charge 24k), and it is holographic (Brown and Henneaux 1986).
Theorem A costs almost nothing there: with no local gravitational field, there is no mediator for theorem B to forbid, and the BMV test
has nothing to measure. What remains is that DMP forbids superpositions of different global geometries (two black hole masses), a
superselection rule with no local test. So in 2+1 the verdict softens from "refuted by experiment" to "a no in principle that no local
experiment can see". Two cautions: whether pure 3D quantum gravity exists as a consistent theory is still open (Maloney and Witten 2010),
and our universe is not 2+1, since gravitational waves, the local degrees of freedom 2+1 lacks, are measured (Abbott et al. 2016).
**Effect on the verdict for our universe: none. For a 2+1 universe: CAN, up to one superselection rule on the global geometry.**

**The owner, 14:01Z, verbatim:** "That is why DMP is the protocol and QG is the specification derived from it."

Assessed: the direction is right, the name is not. What can be derived from DMP is a specification of gravity, and theorems A and B fix
which one: classical geometry between parts over quantum content inside them (in 3+1 the class of Jacobson and Oppenheim; in 2+1
nearly all of quantum gravity, section 8 above). Naming that specification "quantum gravity" would contradict X4, the one property the
name refers to. The paper can say that DMP derives a specification of gravity and that the specification is classical between parts,
which a positive test of gravitationally mediated entanglement in our 3+1 world would refute.

## 9. The owner's replies to the cold read, integrated where they can be

Team Fable assessed the owner's replies to its thirteen conflicts and eight divergences (gravity#22 section 7) and integrated none.
The owner, 14:30Z: "FYI, because fable simply refused to integrate them". Here each reply is read with the assembly of section 2 in
hand, and integrated wherever it fits without breaking a measurement.

| Id | The owner's reply, in short | Integrated? | How, or why not |
|---|---|---|---|
| Q1 | "Dependency chain originating from G0" | Yes | The tree of histories (section 8, Everett): siblings are alternatives, not events, so no spacelike pair is owed. A causal order inside one branch is still needed (X5). |
| Q2 | Unless two are one, it collapses into its information, which returns to the fields it correlates with | Yes | The collapse is real and is check [4]'s fidelity 0.5 when both halves read the content. The halves need not read it: reading existence only (the syndrome) collapses nothing, so two independent witnesses stay. Section 3. |
| Q3 | "One can never vote, so everything has to be at least two" | Half | Geometry acts on paths (routing as geodesics) and never on trust. Section 3. |
| Q4 | The WKHs are pure information, they are because they have to be | Yes, abstracted | The owner's own abstraction (14:08Z): the same start always gives the same chain. No constant is asserted. The absence (no derived number) stays. |
| Q5 | Friction between existence and anti-existence | Half | The pair picture of Hawking radiation, or a firewall (Almheiri, Marolf, Polchinski and Sully 2013); no temperature follows, so the absence stays. |
| Q6 | "Axiom" | Open | Possible as an axiom once it names a metric and a speed; it costs T32's two clauses. |
| Q7 | What it cannot contain leaves as the leak of its storage medium; bits rot | Yes | Dispersal at Landauer's price, destruction as inaccessibility (Harlow and Hayden 2013). Unitarity is kept. Section 3. |
| Q8 | Vector field against stacked scalar fields, tick rates log/ln | No | A constant ratio of tick rates is periodic; Lorentz invariance needs random sprinkling (Bombelli et al. 1987). |
| Q9 | Information goes where it is more optimal; superconductors | No as written | See D8 below for the reading that does fit. |
| Q10 | The clock is the core duality's Planck time; every information quantum carries that energy | No | A bit costs kT ln 2 (Toyabe et al. 2010), about 10^-30 of the Planck energy at room temperature. |
| Q11 | The stage votes only through its existence | Yes | The gate checks existence only (section 2), so the stage enters as membership, never as a vote. |
| Q12 | "I can not refute that" | Stays | X5, no classical limit yet. |
| Q13 | The facts led the model the right way; Hawking radiation is unexplained | Half | Hawking radiation is explained (Hawking 1975); the fate of the information is what is open. The model has no number yet; the candidate is the cosmological constant (Sorkin's 1/sqrt N, a separate piece of work). |
| D1 | The boundary radiates its friction both ways, equilibrium kept | No | Three solar masses left GW150914 (Abbott et al. 2016). |
| D2 | Decay pumped to a different reality relieves the pressure | No | The measured sign (spin lowers the area) is not produced. |
| D3 | Information = force-carrying particles | Yes, by dropping E18 | Force carriers travel at c and cost energy; that is the measurement. |
| D4 | A fact must be asserted to exist | No | The waveform gave the masses to every detector, unasked. |
| D5 | 2.42 is plausible, expected 2.6 to 2.8 | Yes, with the source named | The assembly gives 2 sqrt 2 = 2.83 for ideal content (check [5]); 2.42 is that value lowered by experimental imperfection. The 2.6 to 2.8 expectation is the quantum range. The number comes from quantum mechanics carried as content, not from DMP, and the ceiling is Cirel'son's 2 sqrt 2, not 3. |
| D6 | Effect = strength of assertion times frequency | No | Landauer's price does not depend on the carrier's frequency. |
| D7 | Oscillon decay explains flatness | No | Oscillons form after inflation (Amin et al. 2012); accelerated expansion drives curvature to zero (Guth 1981). |
| D8 | Low existence lets information assemble into its most efficient formation (14:33Z) | Yes | Below: existence = thermal agitation; the condensate is the most efficient formation. |

**Superconductors, the owner's reading (corrected 14:33Z, verbatim):** "When the Existence in a system becomes so low, that it can no
longer hinder the information to assemble into the most efficient formation." This holds, and it is the textbook mechanism in other
words. A phase transition is decided by the free energy F = E - TS: above the critical temperature the thermal term TS (disorder) wins
and the electrons stay unpaired; below it, thermal agitation can no longer break the pairs and the system falls into its most efficient
formation, the condensate in which every Cooper pair shares one phase (Bardeen, Cooper and Schrieffer 1957; Landau's theory of phase
transitions). The dictionary entry is "existence in a system = its thermal agitation, kT". It fits DMP's other readings: a Cooper pair
is two electrons bound into one unit, a Duality (the flux quantum h/2e measures its charge as 2e), and the energy gap is a gate that
refuses every scattering act cheaper than breaking a pair, so no resistance appears. What the entry still owes is its number: BCS
derives the gap at zero temperature as 1.764 kT_c, and a DMP derivation would have to produce that factor. (An earlier reading here took
the sentence of Q9, "the rate of information sharing becomes so low", as the claim; the owner's correction replaces it.)

**Tally after integration.** Of thirteen conflicts: five integrated (Q1, Q2, Q4, Q7, Q11), three halves (Q3, Q5, Q13), one open
(Q6), three not integrated (Q8, Q9 as written, Q10), one conceded (Q12). Of eight divergences: three integrated (D3, D5, D8), five stand.
None of this touches section 4: the wall is Observability, and the verdict stays CAN NOT for our universe.

## 10. Second pass: the wall attacked, and the verdict revised to CAN

The owner, 13:29Z, asked again in a fresh thread for one of CAN, CAN NOT or undecidable, with a conclusion he can accept. This pass was
asked to try first to break theorem A. The theorem holds. The step from it to "X4 fails" does not, and that changes the verdict.

### 10.1 Where the first pass went wrong

Section 4 ends: "Any assembly in which a DMP structure is the geometry predicts that gravity never entangles two masses ... Any assembly
in which no DMP structure is the geometry leaves gravity inside a part ... There is no third place for the geometry to sit." There is a
third place, and physics uses it every day. The geometry splits into a **background** and a **fluctuation** (the background field method;
DeWitt 1967). The background is a DMP structure: the layout, the trust field and the counts, all classical, as theorem A says. The
fluctuation, the linearised metric that carries the Newtonian pull between two lab masses, is **content between parts**. Content between
parts is not "inside a part": section 2 already lets it be entangled across parts (check [5]), and Axiom 3 governs how it moves (only by
a grant, never copied). The first pass counted X1 as met because quantum content was allowed; X4 has to be scored by the same rule.

The experiment X4 names needs nothing more. The entanglement Bose et al. and Marletto and Vedral proposed follows from linearised quantum
gravity on a fixed background, locally mediated and Lorentz-invariant (Christodoulou, Di Biagio, Aspelmeyer, Brukner, Rovelli and Howl,
*Phys. Rev. Lett.* 130, 100202, 2023). The background never has to be in superposition for it.

### 10.2 Why the records do not spoil it: Axiom 3's existence clause

Galley, Giacomini and Selby forbid entanglement only when the mediator is classical. The question is whether DMP's records make the
fluctuation classical by writing down which branch it is in. They do not, because of one sentence DMP already has: "From trust nothing can
be derived about information but its existence: a standing, a refusal or a count says that information is there, never what it says."

- **Lean** (`evidence/Dmp/Blind.lean`, on the gate and record of `Record.lean`): when each witness's evidence depends on existence and
  time only, two runs whose contents agree on existence leave the same record and the same count of performed acts
  (`blind_record_same`, `blind_entry_same`). Drop the clause and a witness that reads one content observable writes it into the record
  (`sighted_record_carries`). Check script: 246 theorems, none resting on more than Lean's standard foundations.
- **Run** (`assembly.py` check [7]): three [[5,1,3]] parts in a row, mass A, the mediator M (one mode of the metric fluctuation, as
  content) and mass B. Three grants (A to M, M to B, A to M); before each, both witnesses of both parts read the syndrome themselves; every
  act is recorded with both readings and its verdict, and the demand count per part is the layout's input. For all 16 pairs of mass
  contents the record and the counts are identical (counts 2, 3, 1), and the two masses end entangled with negativity 0.5, the same as an
  unobserved mediator in check [6]. The control: if a count said which part holds the mass ("information is there" per position), the
  negativity is 0.

So the masses are recorded as being there, and the acts are recorded in full, and still nothing records where the masses are. That
needs one construction choice, which quantum field theory already makes: **existence is the field register of each part, which is always
there; the particle is its content** (an occupied or an empty mode). A DMP that called the particle itself "the information that is
there" would decohere every mass by position; that reading is refuted by every interference experiment with massive molecules, so the
assembly takes the field reading.

### 10.3 What theorem A actually found: the area term

Theorem A says every structure DMP defines between parts is held in full by both halves and commutes with what either half can do. In
holographic codes exactly one thing has that property: the **area operator**. Harlow (*Commun. Math. Phys.* 354, 865, 2017) proved that in
any quantum error-correcting code the quantum Ryu-Takayanagi formula holds as S(A) = ⟨area⟩ + S(bulk), where the area is an operator in the
**centre** of the two complementary wedge algebras: both sides hold it, and it commutes with everything either side can do. That is
"recomputed by both halves of the layer and never by one". DMP's classical structures are not where DMP fails quantum gravity; they are the
part of quantum gravity that is classical in quantum gravity too. This is why the assembly **models** and does not only **host**: a bare
channel that carried a quantum gravity simulation as payload would give no Ryu-Takayanagi formula, no reconstruction from any three of
five and no area term; DMP's gate, record and tree give all three, and the payload gives the dynamics.

### 10.4 The verdict, scored against section 1

| Id | Expected of quantum gravity | Second pass | Carried by |
|---|---|---|---|
| X1 | Quantum content, correlations up to 2√2 | Met | checks [4], [5] |
| X2 | Entropy = minimal surface | Met on the tree (p-adic); the area term is DMP's shared record (10.3) | check [2]; Harlow 2017 |
| X3 | The bulk is an error-correcting code | Met | check [3] |
| X4 | Gravity can be in superposition and entangle two masses | Met, at the order the experiment probes (linearised) | check [7]; `blind_record_same`; Christodoulou et al. 2023 |
| X5 | Classical limit is Lorentzian 3+1 Einstein | Open, as for every discrete model (HaPPY, MERA, causal sets, spin foams) | section 1 already said X5 cannot decide alone |

**Verdict: CAN.** DMP 0.9.8, as written, can be assembled to model what is expected of quantum gravity at the standard the published
models are held to. What it does not do, and no code model does: derive the dynamics or the constants (G, ħ, Λ); those come in as content.
Whether any discrete model reaches our 3+1 world is open for all of them, and that part is the honest vibe: nothing in DMP blocks it, and
nothing in DMP builds it yet.

### 10.5 What DMP still forbids, and why it is not a no

Two geometries that differ in a record (two macroscopically different backgrounds) cannot interfere until the record is gone, and Axiom 3
lets a record be destroyed only by both halves, on the legal date. Quantum gravity allows such interference in principle; in practice
decoherence suppresses it for any macroscopic geometry (Kiefer 1987; Halliwell 1989, section 8's references), and no proposed experiment
can see it. It is a governance rule on erasure, not a physical wall: in principle both halves together may erase.

### 10.6 What this changes for the paper

Section 7's stance ("DMP sits on the classical side; a positive BMV result refutes it") is withdrawn. DMP can be assembled classical
(the first pass: geometry as a DMP structure) or quantum (this pass: the fluctuation as content), so **DMP does not predict the outcome of
a BMV experiment**; nature picks the dictionary. The sentence the evidence now supports: *DMP's shared structures are classical and play
the role of the area term in the quantum Ryu-Takayanagi formula; its existence clause keeps every record blind to content, which is what
lets gravity's quantum part entangle masses through it. Assembled as a holographic code it models the kinematics of holographic quantum
gravity; it derives no dynamics and no constant.* The refuter: a proof or measurement that gravity-mediated entanglement needs the
background itself in superposition, at an order an experiment can reach.

### 10.7 The owner's framings, against this pass

- **DMP as universal IO.** Holds, and is now exact: the IO layer (gate, record, layout) is the classical centre, the payload is quantum.
- **Causality as the existence vector, the tree of histories.** Corrected by `blind_record_same`: the chain of acts does not branch with
  the content. One record chain runs over all branches; the branching (section 8's Everett reading) lives in the content beneath it.
- **WKHs as "same start, same chain".** Holds literally: same start and same acts give the same record for every content.
- **The arrow as the highest-value path.** Fits as the direction the layout moves (fewest hops); the arrow of time is the record's growth
  (records outlive acts).
- **Superconductors** (14:33Z). The condensate is a coherent content state across the whole sample; it survives because no act records
  which pair is where: the gap refuses every scattering act cheaper than breaking a pair, so no record forms. Same mechanism as check [7].
- **"One must always be 2 and one can never be"** (14:38Z). In quantum words: no-cloning (one copy cannot become two) and purification
  (every state is half of a pure pair). Both hold in the assembly.
- **"Every duality is in itself DMP complete, if one holds, all hold"** (14:40Z). In the assembly every tile is the same perfect tensor,
  so a check on one tile is a check on all; that holds for the code, not yet as a theorem about DMP-completeness.
- **The Existence Turing machine and "CAN NOT model, CAN host"** (the first thread's wording). Hosting is Deutsch's universality (1985):
  any quantum dynamics runs as content. This pass says more than host, for the reason in 10.3.

### 10.8 The open lead: a count N and Λ ~ 1/√N, against DESI

Sorkin's argument (from 1987; *Int. J. Theor. Phys.* 36, 2759, 1997): if the count of elements N fixes the four-volume only up to Poisson
noise √N, the cosmological constant, conjugate to the volume, fluctuates as 1/√N. With N the Planck four-volumes in a Hubble four-volume,
check [8] gives N = 5.2e243, 1/√N = 1.4e-122, measured Λ = 2.9e-122 (Planck units): the right order, as Sorkin said before 1998.

**Not DMP-derived.** DMP supplies the count (every act is recorded and "any other reader sees the counts always"), but the 1/√N comes from
the Poisson spread between count and volume, and DMP's layout is "the median of that demand", placed deterministically: spread zero
(check [8]). So in DMP as written, Λ ~ 1/√N does not follow; it would need random placement, which changes Axiom 3. **Against DESI:** DR2
BAO with supernovae prefers evolving dark energy (w0 > -1, wa < 0) at 2.8 to 4.2σ (DESI Collaboration, arXiv:2503.14738, 2025). A
fluctuating Λ allows that but does not predict those numbers; earlier fits of Everpresent Λ (Zwane, Afshordi and Sorkin 2018; Das,
Nasiri and Yazdi 2023) are consistent with the older data, and no published fit to DR2 was found. The lead is closed for DMP as written and
open only with that change.

## References

Checked on the publisher's or arXiv's page on 2026-10-27 where marked (c); the others are standard results cited in gravity#19 and #22.

- H. Barnum, C. M. Caves, C. A. Fuchs, R. Jozsa, B. Schumacher, "Noncommuting mixed states cannot be broadcast", *Phys. Rev. Lett.* 76, 2818 (1996) (c)
- T. D. Galley, F. Giacomini, J. H. Selby, "A no-go theorem on the nature of the gravitational field beyond quantum theory", *Quantum* 6, 779 (2022) (c)
- J. Oppenheim, "A postquantum theory of classical gravity?", *Phys. Rev. X* 13, 041040 (2023) (c)
- M. Heydeman, M. Marcolli, I. Saberi, B. Stoica, "Tensor networks, p-adic fields, and algebraic curves: arithmetic and the AdS3/CFT2 correspondence", *Adv. Theor. Math. Phys.* 22, 93 (2018) (c)
- S. S. Gubser, M. Heydeman, C. Jepsen, M. Marcolli, S. Parikh, I. Saberi, B. Stoica, B. Trundy, "Edge length dynamics on graphs with applications to p-adic AdS/CFT", *JHEP* 06 (2017) 157 (c)
- Y. Rabinovich, R. Raz, "Lower bounds on the distortion of embedding finite metric spaces in graphs", *Discrete Comput. Geom.* 19, 79 (1998) (c)
- F. Pastawski, B. Yoshida, D. Harlow, J. Preskill, "Holographic quantum error-correcting codes", *JHEP* 06 (2015) 149
- A. Almheiri, X. Dong, D. Harlow, "Bulk locality and quantum error correction in AdS/CFT", *JHEP* 04 (2015) 163
- S. Ryu, T. Takayanagi, *Phys. Rev. Lett.* 96, 181602 (2006)
- R. Laflamme, C. Miquel, J. P. Paz, W. H. Zurek, "Perfect quantum error correcting code", *Phys. Rev. Lett.* 77, 198 (1996)
- D. Harlow, P. Hayden, "Quantum computation vs. firewalls", *JHEP* 06 (2013) 085
- X. Dong, D. Harlow, D. Marolf, "Flat entanglement spectra in fixed-area states of quantum gravity", *JHEP* 10 (2019) 240
- F. G. S. L. Brandão, M. Piani, P. Horodecki, "Generic emergence of classical features in quantum Darwinism", *Nat. Commun.* 6, 7908 (2015)
- W. K. Wootters, W. H. Zurek, *Nature* 299, 802 (1982); D. Dieks, *Phys. Lett. A* 92, 271 (1982)
- S. Bose et al., *Phys. Rev. Lett.* 119, 240401 (2017); C. Marletto, V. Vedral, *Phys. Rev. Lett.* 119, 240402 (2017)
- J. F. Donoghue, "General relativity as an effective field theory", *Phys. Rev. D* 50, 3874 (1994)
- T. Jacobson, *Phys. Rev. Lett.* 75, 1260 (1995); *Phys. Rev. Lett.* 116, 201101 (2016)
- L. Bombelli, J. Lee, D. Meyer, R. D. Sorkin, *Phys. Rev. Lett.* 59, 521 (1987); R. D. Sorkin, *Mod. Phys. Lett. A* 9, 3119 (1994)
- B. S. Cirel'son, *Lett. Math. Phys.* 4, 93 (1980); B. Hensen et al., *Nature* 526, 682 (2015)
- J. Myrheim, "Statistical Geometry", CERN preprint (1978)
- J. J. Halliwell, "Decoherence in quantum cosmology", *Phys. Rev. D* 39, 2912 (1989); C. Kiefer, "Continuous measurement of mini-superspace variables by higher multipoles", *Class. Quantum Grav.* 4, 1369 (1987)
- J. B. Hartle, S. W. Hawking, "Wave function of the Universe", *Phys. Rev. D* 28, 2960 (1983); M. J. Duff, L. B. Okun, G. Veneziano, "Trialogue on the number of fundamental constants", *JHEP* 03 (2002) 023
- S. Deser, R. Jackiw, G. 't Hooft, *Ann. Phys.* 152, 220 (1984); E. Witten, "2+1 dimensional gravity as an exactly soluble system", *Nucl. Phys. B* 311, 46 (1988); E. Witten, "Three-dimensional gravity revisited", arXiv:0706.3359 (2007); A. Maloney, E. Witten, *JHEP* 02 (2010) 029; J. D. Brown, M. Henneaux, *Commun. Math. Phys.* 104, 207 (1986); B. P. Abbott et al., *Phys. Rev. Lett.* 116, 061102 (2016)
- H. Everett III, "'Relative state' formulation of quantum mechanics", *Rev. Mod. Phys.* 29, 454 (1957)
- R. P. Feynman, "Space-time approach to non-relativistic quantum mechanics", *Rev. Mod. Phys.* 20, 367 (1948)
- M. Gell-Mann, J. B. Hartle, "Quantum mechanics in the light of quantum cosmology", in *Complexity, Entropy and the Physics of Information* (1990)
- D. Harlow, "The Ryu-Takayanagi formula from quantum error correction", *Commun. Math. Phys.* 354, 865 (2017), arXiv:1607.03901 (c)
- M. Christodoulou, A. Di Biagio, M. Aspelmeyer, Č. Brukner, C. Rovelli, R. Howl, "Locally mediated entanglement in linearized quantum gravity", *Phys. Rev. Lett.* 130, 100202 (2023), arXiv:2202.03368 (c)
- B. S. DeWitt, "Quantum theory of gravity. II. The manifestly covariant theory", *Phys. Rev.* 162, 1195 (1967)
- D. Deutsch, "Quantum theory, the Church-Turing principle and the universal quantum computer", *Proc. R. Soc. A* 400, 97 (1985)
- R. D. Sorkin, "Forks in the road, on the way to quantum gravity", *Int. J. Theor. Phys.* 36, 2759 (1997)
- DESI Collaboration, "DESI DR2 Results II: Measurements of baryon acoustic oscillations and cosmological constraints", arXiv:2503.14738 (2025) (c)
- N. Zwane, N. Afshordi, R. D. Sorkin, "Cosmological tests of Everpresent Λ", *Class. Quantum Grav.* 35, 194002 (2018); Y. K. Das, A. Nasiri, Y. K. Yazdi, "Aspects of Everpresent Λ (II)", arXiv:2307.13743 (2023) (c)
