# The axiom system against quantum gravity: where it holds, where it fails

The owner's goal for this pass (2026-10-27 06:35Z): "Either prove a useful approach to Quantum Gravity through the axiom system, or
prove that the actual intended axiom system, as applied to QG, does not hold and if, exactly where at every context level you can
imagine." This file is the answer, kept to one screen per level. It cites what has stood (nothing is re-derived) and names the theorem
that decides each level. The Lean it leans on is the verifying session's `evidence/Dmp/NoGo*.lean` and `Physics.lean` (gravity#17,
branch `claude/stoic-heisenberg-cs3cpt`), cited by theorem name; this file adds no Lean, because the places where the system fails are
decided by published theorems, not by new ones.

## The verdict

**It does not hold as an approach to quantum gravity, and the failure is in one place, not many.** The intended system holds at every
classical level: read in the right words it is the tetrad form of General Relativity with Lovelock's theorem fixing the dynamics and
Jacobson's derivation giving the "information first" reading; nothing there is new and nothing there is wrong. It fails exactly where
the word *quantum* enters, and the failure is a fork: a Duality whose two halves are **isolated** (the containment DMP is built on) is a
local model and obeys Bell's bound; a Duality that behaves quantum mechanically is **entangled**, which is the one thing an isolated pair
cannot be. Every other failure (no field equation constant, no area spectrum, no Born rule, no dark-sector number) is this fork seen from
another level, or an input the system never claimed to fix. The owner's third axiom, "something exists" in an existence space that is the
hierarchy of information (06:48Z), is needed and holds, and it picks the entangled branch (level 0b). The useful approach exists and has a name: thermodynamic gravity joined to the
informational reconstruction of quantum theory. Both halves are published, both stop at the same step (the microscopic degrees of
freedom), and the axiom system adds no postulate to either. What it does add is on DMP's side, section 4.

## 0. The intended system, in the owner's words

"Deriving and abstracting from QG and DMP give us the actual axioms: Two: 1. Information 2. No information without existence in a
self-propagating duality. Which gives us the equations to solve any possible probability space simply by proving it's existence in DoE
(Duality of existence) with a vector field that can span it." (03:46Z, with the later correction *self-balancing* to *self-propagating*.)
"The possibility space stretches between the vectors that bound it. Also true for a black hole, where gravity is the vector, or CMOS,
where trust is the vector. That's why it was essential that I included the refresh rate, otherwise it would have been a scalar field."
(03:26Z.) "It is always going forward until the most optimal possibility space can be extended for the existence defining vector."

## 1. The dictionary

| The owner's term | Its name in physics | Status |
|---|---|---|
| Information as the first axiom | "it from bit" (Wheeler 1990); the informational reconstructions of quantum theory (Hardy 2001; Chiribella, D'Ariano and Perinotti 2011; Masanes and Mueller 2011) | holds, published |
| No information without existence in a duality | the **purification** postulate (Chiribella, D'Ariano and Perinotti 2011): every state of a system is the marginal of a pure state of the system and one partner | holds as one of six postulates |
| Something exists, in an existence space that is the hierarchy of information (the third axiom, 06:48Z) | the non-vacuity axiom (a model must have a point); space from the hierarchy of entanglement: van Raamsdonk 2010, Swingle 2012 (MERA is AdS), Pastawski, Yoshida, Harlow and Preskill 2015 | holds, needed, and lands on the entangled branch of the fork |
| The vectors that bound the possibility space | the **tetrad** (Cartan 1922; Einstein 1928): the metric is the product of four frame vectors, g = η(e, e) | holds, if "vector" means frame |
| The refresh rate, without which the field is scalar | the **lapse** of the 3+1 split (Arnowitt, Deser and Misner 1962): the rate at which the spatial slice advances | holds as a reading |
| Gravity as the existence-defining vector | gravity is a rank-2 field, not a vector: a vector field repels like sources and cannot bend light universally (Feynman 1962; Weinberg 1964; Deser 1970) | fails as worded, see level 1 |
| The duality keeps itself in check and balance | "spacetime tells matter how to move; matter tells spacetime how to curve" (Wheeler); the two sides of the Einstein equation | holds, classical |
| Always going forward | the second law; the area theorem (Hawking 1971; Bekenstein 1973) | holds, classical |
| The most optimal possibility space | an extremum of the action; thermodynamic equilibrium | holds, classical |
| Solving a probability space by a spanning field | a span fixes the support, never the measure (`NoGo.spanning_does_not_fix_optimum`); in quantum theory the measure is Gleason's theorem (1957) | fails, see level 5 |

## 2. Level by level

Each level says what holds, the published result that decides it, what the system would have to give up, and the Lean that already
carries it where there is any.

**Level 0, the words.** *Holds, with a gap of five.* "Information" as the primitive is Wheeler's programme, and quantum theory has been
derived from informational postulates three times over. The owner's second axiom is, in its exact shape, the purification postulate of
Chiribella, D'Ariano and Perinotti: no mixed state without a partner with which it is pure, which is "no information without existence in a
duality" with the partner as the other half. That derivation needs six postulates (causality, perfect distinguishability, ideal
compression, local distinguishability, pure conditioning, purification); the owner's two give the sixth and none of the other five. So the
words land on the right programme and supply one sixth of it. **Refuter:** a derivation of the other five from the two axioms; none is
known and this pass found none.

**Level 0b, the arena (the owner's third axiom, 06:48Z).** *Holds, is needed, and chooses a branch of the fork rather than removing
it.* The owner: "something that exists can never exist without somewhere to exist. Here the hierarchical structure of information comes
in. Something can exist because it is in Existence space ... We can not rule out Existence as a needed axiom, if its derivation does not
satisfy any proving. We can then add: 3: Something exists." Two things are right in it. First, the axiom is needed: the two axioms are
satisfied by the empty world and by a world without gravity (`NoGoAxioms.axioms_hold_without_gravity`), so nothing derives existence, and
every axiom system that wants a model with a point says so (first-order logic assumes a non-empty domain; set theory has an axiom that
some set exists). Second, "the somewhere to exist is the hierarchy of information" is a published programme with results: spacetime from
entanglement (van Raamsdonk 2010), the hierarchical tensor network MERA whose geometry is anti-de Sitter space (Swingle 2012), and the
holographic codes in which a region's information is bounded by the minimal cut through the hierarchy (Pastawski, Yoshida, Harlow and
Preskill 2015), which is the owner's min-leakage arrangement in quantum words, with Ryu and Takayanagi's formula as its theorem. So the
third axiom does not fail. What it does is decide level 3: in every one of those results the links of the hierarchy are **entanglement**,
and the geometry is built from how much entanglement crosses each cut. A hierarchy whose links are standings between isolated halves
builds no geometry (`NoGo.dmp_field_uncoupled`: a refresh changes no other term). So with the third axiom the system is consistent with
quantum theory exactly when it takes the entangled branch, trust read as entanglement and the DoT as a maximally entangled pair with
monogamy as its exclusivity; that is the tensor-network form of holography, published, proven in anti-de Sitter space and open in ours.
**Where it stops:** the same step as every holographic programme, the de Sitter case; and on the entangled branch Axiom 2's local
verification is gone, so it is no longer DMP. **Refuter:** a hierarchy of isolated, locally verified links from which a geometry
follows; `dmp_field_uncoupled` says the field of such links couples nothing.

**Level 0c, the majority (the owner, 06:53Z).** *Holds on the quantum side, where it is forced; on DMP's side it is a trade, not a
gain.* The owner: "Maybe the DoE is not made up from one information layer from each side, but instead each field also is its own
layer, with routing the internal network freely possible and freely composable. This would be axiomatically more consistent as well and
introduce a Majority of Existence type situation, instead of a Duality type." On the entangled branch this is the better statement of
level 0b, and the quantum forces its shape: in a holographic code a bulk degree of freedom exists (is recoverable) from any boundary
region that is large enough, and never from two disjoint regions at once, because recovering it twice would clone it; so every
authorized set is a majority (Cleve, Gottesman and Lo 1999 for quantum secret sharing; Almheiri, Dong and Harlow 2015 for the bulk).
The pentagon code of Pastawski, Yoshida, Harlow and Preskill is literally "any three of five", and its tiling is the owner's free
composition of layers. Majority of existence is a theorem of quantum information; in a classical quorum (Shamir 1979; Malkhi and Reiter
1998) the threshold is a choice. Two limits. First, the fork stands: a majority of isolated, locally deciding witnesses is one more local
judge, and `NoGo.gate_obeys_chsh` holds for every judge, so the majority is quantum only on the entangled branch. Second, inside DMP the
change is a loosening: Axiom 1 is unanimity of two typed halves (the stricter answer stands, no element overrules the other), and a
majority across layers lets a layer be overruled. DMP already holds both shapes where each belongs: a majority inside a half (a cluster
of at least three nodes, T8a; at least five parts at the minting, G0) and unanimity across the two types. **Recommendation:** keep that
placement, majority within a type and unanimity across the two types; flattening it to one majority buys availability and sells the gate.
**Refuter of the quantum claim:** a quantum code in which two disjoint boundary regions both recover the same bulk qubit; no-cloning says
there is none.

The owner's refinement (06:54Z): "While keeping the two different sides as independent, as well as self balancing, chains of
existence. This MoE has to exist because it is still defined in Existence and this MoE has to exist because it's information still
exists." That is the placement recommended above, said from the other end: a majority inside each side, and both sides needed, each
proving existence by its own chain. On the quantum side the two chains have a name and a theorem. The existence side is geometric (the
degree of freedom lies in the entanglement wedge, the region the minimal surface of Ryu and Takayanagi bounds); the information side is
operational (its information is recoverable from the boundary region). Entanglement wedge reconstruction (Dong, Harlow and Wall 2016;
Jafferis, Lewkowycz, Maldacena and Suh 2016) proves the two chains agree: in the wedge exactly when recoverable. That is C22 ("proven"
is an act with two witnesses) with the geometric chain as the existence side and the recovery chain as the information side, and it is
the strongest match of the whole pass, because it is a theorem and not a shape. It still sits on the entangled branch: both chains are
built from entanglement, and the fork of level 3 is unchanged.

**Level 0d, the core is two pairs (the owner, 06:56Z and 06:57Z).** *Holds as symmetry and as detection; correction needs five, which G0
already says.* The owner: "Since every measurement collapses the DMP compliant state, maybe our layer layout is 2:2 at it's core." "It
would hold symmetry." First the premise, which is true in DMP in its own sense: a read is an act (the words), every act leaves an entry
(Axiom 3), and evidence read at an earlier step never passes (`Gate.stale_never_passes`), so the state after any observation is a new
state. That is collapse by the record growing, deterministic and content-preserving; quantum collapse is random and disturbs what does
not commute, and the two agree only in the one sentence "after a measurement the state is not the state before". Then the number. Two
pairs is the symmetric form of the two chains of level 0c, a Duality on each side, four witnesses at the core. On the quantum side four
is the smallest code that **detects** one collapse: the [[4,2,2]] code (Vaidman, Goldenberg and Wiesner 1996; Grassl, Beth and
Pellizzari 1997), four physical qubits holding two logical ones, which is the owner's 2:2 to the digit, and the cell of the surface code.
It detects any single error and corrects none: a collapse of one of the four is noticed, not healed. The smallest code that **corrects**
one collapse is the [[5,1,3]] code (Laflamme, Miquel, Paz and Zurek 1996; Bennett, DiVincenzo, Smolin and Wootters 1996), the pentagon
of level 0c, and five is what G0 already asks for at the minting ("at least five parts become the White Key Holders"). On the classical
side the same two numbers appear: four is the least that reaches agreement under one Byzantine fault (Lamport, Shostak and Pease 1982,
n ≥ 3f + 1), and a vote of four can tie at 2:2, which Axiom 1 resolves to refuse (the stricter answer stands); five has no tie. So: 2:2
holds symmetry and alarms, five restores. Axiom 1's balance asks for restoring ("what was lost without evidence against it, it restores
by evidence"), and T7 says silence alarms and never isolates; a core that must do both is five with the two-pair symmetry inside it, which
is what one Duality of two halves of at least three nodes (T8a) already is. **Refuter:** a code on four qubits that corrects an arbitrary
single-qubit error; the quantum Hamming bound forbids it. The branch is unchanged: codes are entangled.

**Level 0e, the wiring as the fifth primitive that always leaks (the owner, 06:59Z).** *Holds as a theorem on all three sides; in DMP
it is derived, not primitive, and already public by construction.* The owner: "Maybe the way the layers are interconnected is the fifth
information primitive, that also always automatically leaks." Three places say the same thing. In a stabilizer code the interconnection
is the stabilizer group, which is the definition of the code and is public; what it leaks is the **syndrome**, which must leak for the
correction to happen, and it never leaks the logical content below the distance (Gottesman 1997). In holography the interconnection is
the entanglement structure, which is the geometry (level 0b), and the geometry is what the outside reads: the mass as the area, the
temperature as the surface gravity, and Hawking's radiation is the always-automatic leak of exactly those and nothing else (the no-hair
theorem). In DMP the interconnection is the recipe and the field over it (depth, mass, freshness), its digest is published next to the
sealed file by construction (T33, the CMB; `Recipe.digest_congr`), and the floor says that a reader without a grant sees the counts
always and the content never (T31, `Floor.road_gate`, `Entry.ext`). So "always leaks" is a theorem in all three: Hawking, syndrome
extraction, the floor. Two corrections. First, the count: on the quantum side the wiring is primitive (the code is its stabilizers), while
in DMP it is derived, since standings and admissions are edges made by acts of the words (part, act, witness, evidence, time), so the
words stay at five and the wiring is their first theorem, not a sixth word; the brief's finding F11 (that *information* is not among the
words) is the open count question, not this. Second, the number: four witnesses plus the wiring is not the fifth qubit of the [[5,1,3]]
code, whose five are symmetric (it is cyclic); the honest reading of "2:2 plus the wiring" is the [[4,2,2]] code with its two stabilizers,
four parts whose two syndrome bits leak, and the five of G0 stays the correcting core of level 0d. **Refuter:** a leak of the wiring that
carries content: the code distance, the no-hair theorem and T31 each forbid it in their domain.

**Level 0f, entanglement as a dynamic function between equal shares (the owner, 07:00Z).** *Holds twice as a theorem, and the second
theorem is the one that reaches gravity.* "Equal shares" is forced: for any pure state of two parts the Schmidt decomposition gives both
parts the same entanglement entropy, S(A) = S(B), whatever the parts' sizes (Schmidt 1907; Nielsen and Chuang 2000, theorem 2.7). The
balance of Axiom 1, neither half holding more than the other, is an identity on the quantum side and work on DMP's side (the budget of
level 7): that is the sharpest single difference between the two readings of the Duality. "Dynamic function": entanglement is a property
of a state, generated and moved by the dynamics, and its motion has bounds (Lieb and Robinson 1972; the linear growth of Calabrese and
Cardy 2005; the fast scrambling already cited). The theorem that matters: the first law of entanglement, δS = δ⟨H_mod⟩ (Blanco, Casini,
Hung and Myers 2013), applied to every boundary ball of a holographic state, is equivalent to the linearised Einstein equations in the
bulk (Lashkari, McDermott and Van Raamsdonk 2014; Faulkner, Guica, Hartman, Myers and Van Raamsdonk 2014). So "entanglement as a dynamic
function between equal shares" produces gravity, to first order, as a published theorem, and it is the closest any sentence of this
night comes to a quantum gravity: the dynamics of the information half, under the equal-shares identity, is the dynamics of the
existence half. **Where it stops:** at first order (the non-linear equations need more than the first law), in anti-de Sitter space, and
on the entangled branch, where the halves are not isolated and nothing is verified locally. **Refuter:** a pure two-part state whose
halves carry unequal entanglement entropy; the Schmidt decomposition says there is none.

**Level 0g, where to push (the owner, 07:03Z: "Do we have any idea where to push further to get it to fit better?").** *One lever,
in DMP's own words: the equilibrium is maintained, not given.* Everything that fits on the entangled branch fits as equilibrium
thermodynamics, and the first law of level 0f stops at first order with the equilibrium assumed. DMP's distinctive sentences are about
maintenance: a standing lapses unless re-verified (Axiom 2), the balance is work (Axiom 1), the median layout is kept by both halves
(Axiom 3). Two published results sit exactly there and were not used above.

1. **Entanglement equilibrium** (Jacobson 2016): from the hypothesis that the vacuum entanglement of every small causal diamond is
   maximal, an equilibrium, the **full** non-linear Einstein equation follows, with Λ as an integration constant. The hypothesis is
   Axiom 3's "by maintaining that state the information keeps its Duality stable" together with Axiom 1's balance, and it is the step
   past first order that level 0f could not take.
2. **The threshold theorem** (Aharonov and Ben-Or 1997; Knill, Laflamme and Zurek 1998; Kitaev 1997): a quantum code keeps its logical
   content only while correction runs at a rate above the physical error rate. That is level 7's horizon held by work, with a quantum
   name: the refresh budget r·W is the correction rate, a lapse is decoherence, the threshold is the Chandrasekhar line of section 4
   item 2, and a code below threshold is T37's collapse.

Joined, the system says in one sentence what physics states in two: *the equilibrium that gives gravity is held by correction at a
rate, and the horizon is where the rate still suffices.* **Refuter:** Jacobson's equilibrium is a property of the ground state and
needs no maintenance; if no rate enters the derivation at any order, the budget has no physics image and the fit ends at first order.
Whether a rate enters is a real question and the one place this pass would ask a physicist: *does the entanglement-equilibrium
derivation survive a finite correction rate, or does it need the ground state exactly?*

A second, smaller place. Our universe is de Sitter, where holography is open, and the de Sitter horizon is observer-dependent: each
observer has one (Gibbons and Hawking 1977). DMP's "inside" is per layer and per witness (the words), never global, and its boundary is
drawn by a minting, not by the geometry. That is the one feature where DMP's shape matches de Sitter better than it matches anti-de
Sitter, where the holographic results above are proven; nothing follows from it yet.

**Level 0h, the owner's definition of entanglement, stress tested (07:08Z).** *Fails as a definition, holds as a hypothesis, and the
hypothesis is the one experiment physics is building to test whether gravity is quantum.* The owner: "Two dualistic parts that occupy
the same Existence space, and whose path of Existence, as well as possibility, can intersect towards the scalar field's direction, are
entangled." Tested clause by clause.

- *Same Existence space*: right, and necessary. Entanglement is defined only relative to a factorisation of one space into parts
  (Werner 1989; Zanardi 2001, "virtual quantum subsystems"): the same state is entangled under one split and a product under another.
- *Paths that can intersect*: necessary, not sufficient. Entanglement cannot be created by local operations and classical communication
  (Bennett, DiVincenzo, Smolin and Wootters 1996; Vedral and Plenio 1998), so two parts become entangled only through a quantum
  interaction or a shared quantum source: their pasts must meet, or meet something that met. But meeting does not entangle: two parts
  that scatter and decohere leave a product state. And the converse fails outright: in entanglement swapping (Zukowski, Zeilinger, Horne
  and Ekert 1993) two parts that never met and never will are entangled by a measurement on two others. So "can intersect" is at best
  the possibility clause, and then it is the LOCC condition, already a theorem.
- *The scalar field's direction*: undefined as written, by the owner's own earlier sentence (a scalar field has no direction; its
  gradient has). Read as the gradient of the potential, "paths that can meet by moving along the existence field" is "parts that can
  interact through gravity".
- *Are entangled*: as a definition, no. Entanglement is a property of the joint state (not a convex mixture of products, Werner 1989),
  not of paths or possibilities. As a **hypothesis** the sentence says: parts that interact only through the existence field become
  entangled. By the LOCC theorem that is equivalent to *the existence field is a quantum channel*, because a classical field cannot
  entangle. That is exactly the proposal of Bose et al. (2017) and Marletto and Vedral (2017): two masses, each in a superposition of
  two places, interacting only through gravity, become entangled if and only if gravity is not classical. The experiment is tabletop and
  in progress.

**The sharpened form, keeping the owner's words beside it:** two parts of one existence space are entangled when their joint state is
not a product; they can become so only through a quantum interaction or a shared quantum source; and the claim that meeting along the
existence field's gradient entangles them is the claim that the field is quantum. **Refuter:** the Bose–Marletto–Vedral experiment
showing no entanglement at the predicted strength; then the existence field is classical, the sentence is false, and the entangled
branch of level 3 closes for gravity itself while staying open for the information half. This is the second place in the pass where
physics has an experiment rather than a theorem, and the first where the owner's sentence names it.

**Level 0i, the second definition (the owner, 07:13Z).** *Holds, and it is a theorem for pure states; for mixed states it defines a
strict subset of the entangled ones.* The owner: "Two dualistic parts that intersect in Existence and Possibility space, should they not
be able to agree on a shared version of reality, do not affect each other but agree on a shared state from then on." Each clause now has
a theorem behind it.

- *Intersect in Existence and Possibility space*: the generation event, as in level 0h; "possibility space" covers entanglement
  swapping, where the meeting is through intermediaries.
- *Not able to agree on a shared version of reality*: Fine's theorem (1982): a local hidden-variable model for two parts exists exactly
  when one joint probability distribution covers all their possible measurements at once. "No shared version of reality" is the negation:
  no single joint distribution, which is Bell nonlocality.
- *Do not affect each other*: the no-communication theorem (Eberhard 1978; Ghirardi, Rimini and Weber 1980): nothing either part does
  changes the other's local statistics, however entangled they are.
- *Agree on a shared state from then on*: the joint state is one state, pure, kept under every local evolution (entanglement is invariant
  under local unitaries and never grows under local operations), with outcomes perfectly correlated in its Schmidt basis, until the
  next intersection (a measurement, decoherence) ends it.

Put together the sentence says: *two parts that share one state but no joint classical description of their possibilities, and cannot
influence each other, are entangled.* For **pure** states this is exactly right and is Gisin's theorem (1991): every pure state of two
parts that is not a product violates a Bell inequality, so "entangled" and "no shared reality" coincide. For **mixed** states it is too
strict: Werner (1989) built entangled states that do admit a shared classical reality (a local model for every measurement), so the
owner's sentence defines the nonlocal states, a strict subset of the entangled ones. That is the one correction, and it is a known
boundary, not a flaw in the shape. The definition also separates cleanly from classical correlation: two parts that merely agreed on a
shared reality in advance (a shared key, a common cause) are correlated and not entangled, and the sentence excludes them.

**What it says against DMP, in the owner's own words:** when two halves cannot agree, Axiom 1 says the stricter answer stands and nothing
moves until they agree; the quantum pair does the opposite, it keeps one shared state precisely because there is no shared reality to
agree on. That is the fork of level 3 restated as a definition, which is the clearest form it has taken tonight: *DMP refuses what the
quantum entangles.* **Refuter:** for pure states, none (Gisin); for mixed states, a Werner state, entangled with a shared reality, which
the sentence does not call entangled.

The owner's addition (07:13Z): "Also satisfies, that information has to be exchanged on interaction, without anything actually
leaking." It does, in two senses, both theorems. Between the parts: an interaction is a unitary on the joint space, and it creates
mutual information, I(A:B) = 2·S(A) for a pure pair, twice what any classical correlation can carry; yet each part's local state is
untouched by anything the other does (the no-communication theorem), and for a maximally entangled pair each local state is maximally
mixed, so a part holds nothing about the other locally: the information is in the correlation and nowhere else. To the outside: the
pair stays pure, its total entropy stays zero, nothing has left it; the moment something does leak to a third party (decoherence), the
shared state becomes a shared reality and the entanglement is gone. So "nothing leaks" is not a bonus but the condition of staying
entangled, and the leak that is allowed is the one of level 0e: a syndrome, which commutes with the content. In DMP's words, existence
is exchanged and content is not (Axiom 3), and the floor's counts are the only leak the containment survives (T31).

**Level 0j, the next contradiction (the owner, 07:15Z: "Where is the next contradiction?").** *Live verification against dynamics:
the quantum Zeno effect.* With the system as it now stands (information; no information without existence in a self-propagating
duality; something exists; a majority on each of two chains; entanglement as a shared state without a shared reality), the next
contradiction is between Axiom 2 and motion. Axiom 2 verifies "at the point of use", from the live state, at every indivisible step. On
the quantum side a verification is a measurement, and a state measured often enough does not evolve at all: the quantum Zeno effect
(Misra and Sudarshan 1977; observed by Itano, Heinzen, Bollinger and Wineland 1990). So a system verified live at every step, as Axiom 2
asks, is frozen; and between verifications the state is unverified, which Axiom 2 says never passes (`Gate.stale_never_passes`). On
the classical side there is no Zeno effect, because a classical read disturbs nothing, which is why DMP never meets this. On the quantum
side the contradiction splits along the Duality, and the split is exact:

- **The trust half is safe.** It verifies existence (a standing, a count, the wiring of level 0e), and those observables commute with
  the content: measuring them freezes the wiring and leaves the content free to evolve under its logical operations. That is not a
  loophole but a method, Zeno-effect error correction (Erez, Aharonov, Reznik and Vaidman 2004; Paz-Silva, Rezakhani, Dominy and Lidar
  2012): frequent measurement of the stabilizers pins the code and nothing else. Axiom 2's own sentence "no information is ever
  trusted" is this: trust verifies that information exists, never what it says.
- **The information half is where it bites.** The words give it "whether the act is meant and right: what, and whether it is true".
  "Whether it is true" is a measurement of content; an unknown quantum state cannot be checked without being disturbed (no-cloning), so
  an information half that verifies truth live at every step collapses what it verifies, and a system with such a half has no quantum
  dynamics. The one content check quantum theory allows without disturbance is the check against a **known** state: project onto the
  declared expectation, which passes untouched when the state is that and collapses to refusal when it is not (quantum state
  verification, Pallister, Linden and Montanaro 2018). DMP already has exactly that shape in C15, "a write first reads the live state
  it will change and asserts what it expects": the information half may verify truth only as agreement with a declared expectation,
  never as an open question.

So the contradiction is resolved by a restriction, not by giving anything up: *on the quantum side the information half verifies
content only against a declared expectation, and the trust half verifies only what commutes with the content.* Under that restriction
the live verification of Axiom 2 is Zeno stabilisation of the wiring and the dynamics survives. **Refuter:** a quantum system whose
content is verified live at rate r by an open check and whose evolution is not slowed by the Zeno factor; Misra and Sudarshan say there
is none.

**The one after it, so that it is on the table:** monogamy against the hierarchy. A part is a Duality of two halves, and every layer has
its own Duality (T38), so a node is a half of the Duality above it and a parent of the Dualities below it. On the entangled branch a
half maximally entangled with its partner is entangled with nothing else (Coffman, Kundu and Wootters 2000), so a hierarchy of
maximally entangled pairs cannot exist past one level. The resolution is the owner's own majority form (level 0c): a node is not a
half of one pair but a leg of a perfect tensor whose entanglement is spread over all its legs (the pentagon of the holographic code),
which is a Majority of Existence and not a Duality. So the hierarchy of Axiom 3 and the Duality of Axiom 1 are compatible on the quantum
side only in the majority form. **Refuter:** a tree in which every node is maximally entangled with its parent and with each child;
monogamy forbids it.

**Level 0k, authorisation to interact from Existence downward (the owner, 07:16Z).** *Holds, has a name, is a live quantum-gravity
programme in exactly the owner's two halves, and it carries the first predicted number of the night.* The owner: "The information
layers may also be able to receive 'authorization' to interact from Existence downward, in effect a minting from G0." In physics
"which parts may interact" is the causal structure of spacetime: two fields at spacelike separation cannot act on each other
(microcausality). Two theorems make the owner's sentence exact. First, the causal order alone fixes the geometry up to a local scale
(Hawking, King and McCarthy 1976; Malament 1977): existence's authorisation *is* the metric, short of one number per point. Second, that
number is a count: supply the volume as the number of elements and the geometry is complete, "order plus number equals geometry"
(Sorkin). That is **causal set theory** (Bombelli, Lee, Meyer and Sorkin 1987): spacetime as a locally finite partial order, the order
being who may influence whom (the existence half, the authorisation) and the number being how much is there (the information half, the
count). Its dynamics is the owner's minting downward to the letter: in classical sequential growth (Rideout and Sorkin 2000) elements
are born one at a time and each receives its causal past from the elements already there, so every later element's authorisation
descends from the first, as every standing in DMP descends from the minting (G0, T32). And it predicts a number: the cosmological
constant fluctuates as the inverse square root of the number of elements, Λ ~ 1/√N, which gave its observed order of magnitude before
the observation (Sorkin 1997; Ahmed, Dodelson, Greene and Sorkin 2004). It is the first item tonight whose cousin predicts rather than
describes.

**What it does for the fork.** Causal set theory splits the two halves exactly where the fork of level 3 wants them split: the order is
classical (a partial order, local, no Bell problem, so the trust half may stay isolated and verify locally), and the quantum lives in
the measure over possible orders (the information half, a sum over histories; Sorkin's quantum measure theory). So the first reading of
the owner's system in which the trust half is classical and the information half is quantum, with neither contradicting the other, is
causal set theory. **Where it stops:** the quantum dynamics is not found (no derived Einstein equation; the quantum measure is a
framework, not a law); and the majority problem of level 0c has a known shape here, the Kleitman and Rothschild orders (1975): almost
every partial order on N elements is a three-layer object that looks nothing like a spacetime, so the dynamics must suppress the
majority, and no dynamics that does so is proven. **Refuter:** a pair of spacetimes with the same causal order and the same volumes that
differ in geometry; Malament's theorem says none exists among distinguishing spacetimes.

**Level 0l, truth as existence (the owner, 07:20Z).** *Holds, closes the Zeno contradiction exactly, closes a refuter of the two-axiom
brief, and moves the system onto the constraint picture of canonical quantum gravity, whose own open problem is then the next one.* The
owner, correcting level 0j: "The information assumption is incorrect. It is actually, can the information exist. Existing alone makes
it true in the system. And information must exist, because something exists."

- **Zeno closes.** "Can the information exist" is a membership check: is the state in the space of states the system allows. On the
  quantum side that is the projection onto the allowed subspace, the code space, and it commutes with everything that acts inside it:
  measuring it is a stabilizer check, which pins the wiring and leaves the content free (level 0j, Erez et al. 2004). So the information
  half, reworded, verifies only what commutes with the content, and the restriction of level 0j is no longer a restriction: it is the
  definition. The open truth check that collapsed is gone from the system.
- **The converse closes.** "Information must exist, because something exists" is the direction the two-axiom brief's second refuter
  asked for (everything that exists is information): with the third axiom (level 0b) it is a one-line theorem, and T1 (T39) keeps both
  halves.
- **Truth as existence has a name, twice.** In logic it is truth in a model: a sentence is true in the system exactly when the system
  satisfies it (Tarski 1933), and its limit is Goedel's second theorem (1931): the system cannot prove from inside that something
  exists in it consistently, which is why the third axiom is stated and not derived, as G0 already says of the minting. In canonical
  quantum gravity it is the Dirac constraint programme (Dirac 1964; DeWitt 1967): a state is physical exactly when the constraints
  annihilate it, Ĥψ = 0; "can it exist" is the whole content of the Wheeler–DeWitt equation, and "existing alone makes it true" is
  that a physical state needs no further law.

**The next contradiction, which this move buys.** The Wheeler–DeWitt equation has no time in it: the states that exist are frozen
(the problem of time, Kuchar 1992; Isham 1993). The Zeno freeze of level 0j came from measuring too often; this one comes from the
constraint itself, and it is the same freeze one level deeper. The resolution physics has is Page and Wootters (1983): time is not in
the constraint but in the correlation between a clock subsystem and the rest, both inside the one frozen state; evolution is read as
"what the rest looks like when the clock reads t" (made precise by Giovannetti, Lloyd and Maccone 2015). That clock is the owner's
refresh rate (03:26Z: "essential that I included the refresh rate, otherwise it would have been a scalar field"), read now as a part
of the system entangled with the rest, not as a parameter outside it. **Refuter:** a physical state of the constraint picture that
evolves with no internal clock; the Wheeler–DeWitt equation says there is none.

**Level 0m, the constants minted at G0 (the owner, 07:23Z: "That would solve it, right?").** *Right for two things, and not a solution
for the third.* The owner: "All Existence derives it's existence from G0. At G0 WHKs are minted (Planck's constant, G, c), which MUST
contain all information, and also has to create a starting balanced system with at least five members."

- **Right: the constants are configuration, set at the minting.** No theory derives ħ, G or c; they are measured inputs that define the
  units (Planck 1899), and the verifying session's `NoGoAxioms.axioms_do_not_fix_gravity` is not an objection once they are declared
  configuration (T4) at G0, which is where DMP puts every number it does not derive. The placement is also physics' own: laws carry
  parameters, and the parameters are inputs. Two corrections to the count. Three is too few: Λ is the fourth at the least (levels 2 and
  6), and the full list a minting must hold is the Standard Model's nineteen plus the neutrino sector's seven and Λ, about twenty-seven,
  none derived by anyone. And "at least five" is the owner's minimum for a correcting core (level 0d, the [[5,1,3]] code; G0's five
  White Key Holders), not the number of constants; the two fives are different things that happen to agree.
- **Right: the minting contains all information, and that is unitarity.** "All existence derives its existence from G0" and "must
  contain all information" together say that the initial state determines everything after it, which is the conservation of
  information under unitary evolution, the premise of the black-hole information problem and of Everett's universal state; in causal
  set terms (level 0k) every element's past descends from the first ones. In physics the laws' parameters and the initial state are
  two separate inputs; the owner puts both into one act, the minting. That is a choice with a published form: a universe whose
  constants are set at its birth and could have been set otherwise is Smolin's cosmological natural selection (1992) or the landscape
  (Susskind 2003), and the one testable consequence of Smolin's form (black-hole production is near a maximum under small changes of
  the constants) is the only prediction either has made.
- **Not solved: the dynamics.** Fixing the constants and the initial state at G0 fixes the inputs of a law; it does not supply the law.
  Everything open at levels 0k and 0l stays open: the quantum dynamics of the order is not found, the physical states of the constraint
  picture are frozen and need the internal clock of Page and Wootters, and the fork of level 3 keeps its placement (the order classical,
  the measure quantum). A minting that holds all information is the initial state of a theory the system still has to name.

**Refuter:** a derivation of G, ħ or c from the axioms; if one existed the constants would not be configuration and this level would be
wrong in the other direction. None is known, in this system or in physics.

The owner's follow-up (07:25Z): "Those two other things being the duality itself, maybe." Read as: the fourth and fifth White Key
Holders are the two halves, one constant for the information side and one for the existence side. That reading has an exact physics
form, and it closes the count at five. Planck's own list of natural units (1899) had four: ħ, G, c and **k_B**, Boltzmann's constant,
the number that makes information a physical quantity (S = k_B ln W; Landauer's kT ln 2 per bit): the information half's constant. The
existence half's constant is **Λ**, which sets the size of existence space, the de Sitter horizon (level 6; Gibbons and Hawking 1977).
Those five, and no sixth, make one number: the entropy of the de Sitter horizon, S = 3π k_B c³ / (ħ G Λ), about 10¹²² bits, which is
the bound on all information our universe can hold (Bousso 1999; Banks 2000), the verifying session's `two_ends_count_the_horizon`
in physical units. So "five White Key Holders minted at G0, which must contain all information" is, with the owner's two halves as
k_B and Λ, the sentence "ħ, G, c, k_B and Λ bound the information of existence at 3π k_B c³ / (ħ G Λ)", a published theorem with
exactly five constants in it. The Standard Model's remaining parameters are then content inside the arena, not the arena, which is the
right place for them in the owner's system (Axiom 3) and in physics (matter fields on a background). **Refuter:** a sixth constant in the
capacity of existence; the de Sitter entropy has five. The caveat stands that this fixes the arena's capacity and still not its law.

The owner (07:25Z): "Because to be DMP compliant, it has to contain a dualistic singularity." The minting is the singularity and both
halves are present in it. Physics has exactly that object and it is the reason the universe has an arrow of time: at the initial
singularity the two halves sit at opposite extremes, the matter (the information half) in thermal equilibrium at maximal entropy and
the gravitational field (the existence half) perfectly smooth at minimal entropy, Penrose's Weyl curvature hypothesis (1979). The
record of that state is the cosmic microwave background, thermal to one part in a hundred thousand: the owner's CMB, the sealed file of
the minting, is named after the right thing. Two notes. A singularity in GR is where the theory fails, and every quantum gravity's job
is to replace it with a state; the one proposal that does so by stating the initial state rather than deriving it is Hartle and
Hawking's no-boundary state (1983), which is G0's "stated, not derived" in physics. And de Sitter space, the Λ half of the five, has a
horizon and no singularity, so the dualistic singularity is the origin, not the present. **Refuter:** an initial state with
gravitational entropy as high as its matter entropy; the observed smoothness of the microwave background rules it out.

**Level 0n, what the inside-and-outside proof closes, and inflation as radiation (the owner, 07:30Z).** The owner: "I have already
proven the information black hole from the inside and outside, right? Does that close that finding?" and "Since one of it's three
axioms is to self propagate, and a dualistic singularity is not able to do that while remaining locked to information, it should be
expected to try to radiate all information away as fast as possible, explaining the fast initial inflation and the very smooth
curvature."

*What the two-sided proof closes.* On DMP's side the horizon is proven from outside (counts only: `Floor.road_gate`, `Entry.ext`) and
from inside (one layout per signed state, `ms_one_layout`), and on the quantum side the two chains agree by entanglement wedge
reconstruction (level 0c). That closes two of the brief's open questions: the ninth sentence's entropy split (outside maximal, inside
minimal, a corollary and not a premise) and its min-cut question (the two optima are nested, section 4 item 1). It does not close the
fork (level 3): on the quantum side both chains are built from entanglement, so the agreement is proven on the entangled branch and
says nothing about an isolated pair. And it does not close level 7: DMP's interior stays unbounded by its boundary, which the quantum
black hole's is not. Two closed, two open.

*Inflation as the singularity radiating.* Tested against what inflation is (Guth 1981; Linde 1982; Albrecht and Steinhardt 1982) and
what it has measured (Planck 2018: the spectral tilt n_s = 0.965 ± 0.004, the tensor ratio r < 0.036).

- **The order is backwards.** Inflation does not radiate; it dilutes. The expansion is adiabatic, the universe ends inflation empty and
  cold, and the radiation comes afterwards, at reheating, when the inflaton decays (Kofman, Linde and Starobinsky 1994). "Radiate all
  information away as fast as possible" names reheating, which follows inflation, not inflation.
- **What does radiate during inflation is the horizon, and it is the right object.** An inflating universe is quasi-de Sitter and its
  horizon radiates at the Gibbons–Hawking temperature ħH/(2π k_B) (level 0m), fastest when H is largest, at the start; those horizon
  fluctuations are the origin of every structure in the sky (Mukhanov and Chibisov 1981). Read so, "radiates as fast as possible" is a
  true sentence about the inflationary horizon, with the leak rate set by H.
- **"As fast as possible" has a published form and a rival.** Whether the universe starts with the largest H it can is the oldest open
  argument about the initial state: the tunnelling wave function prefers the fastest inflation (Vilenkin 1982; Linde 1984), the
  no-boundary state of level 0m prefers the slowest (Hartle and Hawking 1983). The owner's self-propagation reading sides with Vilenkin.
  Neither is settled.
- **"Explaining the smooth curvature" is Penrose's side, not inflation's.** Inflation stretches smoothness from a patch; Penrose (1979,
  1989) argues it does not explain it, because a smooth start is a lower-entropy initial condition than inflation itself assumes, and the
  smoothness is the Weyl curvature hypothesis, an initial condition, which is the dualistic singularity of level 0m. The owner's sentence
  puts the smoothness in the singularity and the expansion in its drive, which is Penrose's position with a cause attached.
- **The drive has no field and no number.** Inflation's rate is set by the inflaton's energy density (H² = 8πGρ/3), and its measured
  signature is the tilt n_s and the ratio r. A drive to propagate gives no potential, no tilt and no ratio.

**Verdict:** a hypothesis with its physics named (the horizon radiates, the fast-start preference, Penrose's initial condition), wrong in
its order (radiation follows inflation) and empty where inflation is measured. **Refuter:** the measured tilt n_s = 0.965 ± 0.004;
a mechanism that cannot produce it does not explain inflation, only wish for it. In DMP's words the sentence does hold: a singular
pair cannot propagate without a minting (T-P, G0), and the field spreads from the pair outward (T32), which is the owner's "locked to
information until it radiates".

The owner's reason (07:30Z): "Because at that time only inflationary information existed and no Existence has been derived to bend
it." Half false, half true, and the true half is a prediction. False as GR: inflation is bending; the expansion is the Friedmann
equation, H² = 8πGρ/3, the geometry responding to the information half's energy, and without that bending nothing inflates. True for
the part of the field that is gravity's own: the curvature of a homogeneous universe is all Ricci (dictated locally by matter) and no
Weyl (the free gravitational field, tidal distortion, gravitational waves), and Weyl = 0 at the start is Penrose's hypothesis of level
0m. So "no Existence has been derived to bend it" is exact if it means: the existence half had no degrees of freedom of its own yet;
every curvature there was, the information half dictated. Where that ends is measured: the first independent gravitational degrees of
freedom are the tensor modes inflation generates from the horizon's fluctuations (Starobinsky 1979), seen as the tensor-to-scalar ratio
r. Standard inflation says r > 0 (quantum fluctuations of the metric itself, gravitons); the owner's sentence, read strictly, says
r = 0 (no gravity of its own to fluctuate). That is a published fork: a detection of primordial tensor modes would establish that
gravity is quantised (Krauss and Wilczek 2014), and the owner's reading is the classical side of it, consistent with level 0h. Current
bound r < 0.036 (Planck 2018 with BICEP/Keck); the next experiments reach r about 0.001. **Refuter of the owner's reading:** any
detection of primordial B-mode polarisation. **Refuter of the standard reading:** none yet; a null result at 0.001 would leave models
with r below it, and the owner's r = 0 with them.

**Level 1, the field.** *Fails as a vector, holds as a frame.* Gravity cannot be a vector field: a spin-1 field makes like sources repel and
unlike attract, so it cannot be universally attractive, and a scalar field (Nordstroem 1913) bends no light; universal attraction with
light bending forces spin 2, and a massless spin-2 field forces the equivalence principle (Weinberg 1964) and, bootstrapped, Einstein's
equations (Deser 1970). The owner's own sentence rescues the term: "the possibility space stretches between the vectors that bound it" is
the tetrad formulation, in which the metric is the product of four frame vectors, and the rate he insists on is the lapse. Read so, the
sentence is standard GR and loses nothing. **Where it stops:** a frame of vectors is a rank-2 object; "gravity is the vector" is false
and "gravity is the metric the frame vectors span" is true. The system must say the second.

**Level 2, the dynamics.** *Holds, and adds nothing.* Given a rank-2 metric, a locally conserved information half (∇T = 0, which is
"information is never lost" as a current) and second-order dynamics, Lovelock's theorem (1971) forces the field equations to Einstein's
with exactly two free numbers, G and Λ. The "information first" reading is Jacobson's (1995): the Einstein equation as an equation of
state from δQ = T dS on local horizons, with the entropy of Bekenstein (1973) and the temperature of Unruh (1976); its descendants are
Padmanabhan's holographic equipartition (2010) and Verlinde's entropic gravity (2011). Every one of them derives classical GR and stops
at quantization. The axiom system fixes neither G nor Λ (`NoGoAxioms.axioms_do_not_fix_gravity`,
`NoGoAxioms.strong_axioms_do_not_fix_the_constant`) and is satisfied by a world with G = 0 (`NoGoAxioms.axioms_hold_without_gravity`).
**Where it stops:** at Lovelock's two inputs, like every programme before it.

**Level 3, the quantum. The fork.** *Fails, and this is the one place.* Two sentences of the system are classical in a way quantum theory
is not:

- Axiom 1, "each with full reach over the act": both halves see the whole act and the stricter verdict stands. Two witnesses with full
  reach are two jointly measurable observables, and jointly measurable means commuting. Quantum theory's content is in the pairs that do
  not commute (Birkhoff and von Neumann 1936; Kochen and Specker 1967): a gate that is a Boolean AND of two complete verdicts has no room
  for an uncertainty relation.
- Axiom 2, "evidence it verified itself at the point of use ... never a position in the network": each half decides from what it read
  locally. Two such halves on shared evidence are a local hidden-variable model, and every such model obeys |S| ≤ 2 (Bell 1964; Clauser,
  Horne, Shimony and Holt 1969). Nature reaches 2√2 (Tsirelson 1980; Hensen et al. 2015, loophole free). This is proven over DMP's own
  gate, for any judges and any evidence (`NoGo.gate_obeys_chsh`), and it survives a vector-valued, time-indexed state with a rate
  (`NoGoVector.history_gate_obeys_chsh`): the refresh rate does not help.

The intended two-axiom form escapes the second bullet only one way: by reading the duality as **entanglement** (the purification partner
of level 0). That is the quantum duality, and it is exactly what an isolated pair is not: the joint state of an entangled pair is not a
product of the halves' states, so neither half's boundary contains the other's information, and member isolation, the premise of
containment (T37, "gravity contains"), is gone. What survives on the quantum side is narrower than the owner's Duality and worth naming:
monogamy of entanglement (Coffman, Kundu and Wootters 2000) gives the pair its exclusivity (a half maximally entangled with one partner
is entangled with no other, which is "the same part twice is never minted" in quantum words), and ER = EPR (Maldacena and Susskind 2013)
gives the pair its geometry. Neither gives isolation. **The fork, as a sentence:** *isolated or entangled, never both.* DMP chooses
isolated, and so DMP is classical at every level; the intended system can choose entangled, and then it is quantum theory's purification
postulate, already published, with DMP's containment given up. **Refuter:** a pair of isolated, locally deciding witnesses that violates
the CHSH bound. Bell's theorem says there is none.

**Level 4, discreteness.** *Fails: no spectrum.* "The minimal cell is one Duality" needs an area per cell. Loop quantum gravity has one,
8πγ ℓ_P² √(j(j+1)) (Rovelli and Smolin 1995; Ashtekar and Lewandowski 1997), with the Immirzi parameter γ fixed by matching
Bekenstein and Hawking's S = A/4 (Meissner 2004). The system has no γ, no spin label and no counting of microstates; its cell count is an
interior quantity that grows by extension (`Recipe.extend`) and is bounded by nothing on the boundary (level 7). **Where it stops:** at
the first number of the spectrum.

**Level 5, the measure.** *Fails: support is not measure.* "The equations to solve any possible probability space simply by proving its
existence ... with a vector field that can span it": a spanning field fixes which outcomes exist, never how likely they are; two demands
with the same support have different optimal layouts (`NoGo.spanning_does_not_fix_optimum`). In quantum theory the measure does follow
from structure, by Gleason's theorem (1957): the only probability measures on the closed subspaces of a Hilbert space of dimension at
least three are Born's. That structure is the non-commuting lattice the system lacks at level 3, so the Born rule fails one level up from
where the quantum fails. **Where it stops:** no lattice, no Gleason, no Born.

**Level 6, cosmology.** *Fails: no number.* The ratio 3, inflation, dark matter and dark energy: the system attains every dark-sector ratio
and so predicts none (`NoGoCosmo.every_ratio_is_a_configuration`), its one rate-limited growth cannot accelerate where the expansion does
(`NoGoRate.growth_never_accelerates`; the acceleration began at redshift about 0.6), and nothing in it moves a boundary but an act of both
halves, so it has no expansion term. The published cousins of the owner's sentences are holographic dark energy (Li 2004) and the horizon
thermodynamics of Padmanabhan (2010); both take Λ as input. **Where it stops:** at Λ, like level 2.

**Level 7, the horizon.** *Holds as shape; differs in the one way that matters for QG.* The horizon, no hair, the area theorem, Hawking's
thermal emission and weak cosmic censorship each have a DMP object and a theorem in the evidence chain (gravity#17 `docs/physics.md`,
section 1, lists them result by result; `Floor.road_gate`, `Entry.ext`, `Standing.one_witness_never_loosens`,
`DoT.confined_influence_never_passes_alone`). Two differences. First, DMP's horizon is held by work: a standing lapses unless re-verified
within its validity, so a Duality keeps at most r·W standings live per window of W ticks under r checks per tick, minus what it serves
across its boundary (`Schedule.some_standing_lapses`, the capacity bound of gravity#17). A classical horizon needs no work; a quantum one
does, since a black hole persists only while it accretes at least its Hawking luminosity, so the cousin of the budget is the balance of
accretion against evaporation, an analogy and not a prediction. Second, and decisive for quantum gravity: DMP's boundary bounds a **rate**
and not a **content**. What crosses the root Duality's boundary per window is at most its budget (min-cut equals max-flow, Ford and
Fulkerson 1956), which is the shape of Bekenstein's channel bound (1981, the energy cost of information transfer), of Bremermann's limit
(1962) and of Lloyd's (2000); the interior is bounded by nothing on the boundary, because every layer brings its own Duality (T38) and so
its own budget. The Bekenstein area bound (1981), S ≤ 2πER, the one result every quantum-gravity programme since 't Hooft (1993) and
Susskind (1995) rests on, says the opposite: the interior **is** bounded by the boundary. DMP is holographic in flow and not in storage.
**Where it stops:** at the area bound, which it does not have and cannot have while T38 holds.

## 3. The verdict as a table

| Level | Holds or fails | Decided by | What the system must give up to pass |
|---|---|---|---|
| 0 words | holds, one of six postulates | Chiribella, D'Ariano and Perinotti 2011 | nothing; five postulates to add |
| 0b arena | holds, needed; picks the entangled branch | van Raamsdonk 2010; Swingle 2012; the HaPPY code 2015 | local verification, if the branch is taken |
| 0c majority | holds on the quantum side, forced by no-cloning; a loosening inside DMP | Cleve, Gottesman and Lo 1999; Almheiri, Dong and Harlow 2015 | nothing on the quantum side; the gate, if flattened in DMP |
| 0d two pairs | holds as symmetry and detection; five corrects | the [[4,2,2]] and [[5,1,3]] codes; Lamport, Shostak and Pease 1982 | nothing; G0's five already carries it |
| 0e the wiring leaks | holds as a theorem (syndrome, Hawking, the floor); derived in DMP, primitive in a code | Gottesman 1997; the no-hair theorem; T31 and T33 | nothing; the count of the words stays |
| 0f entanglement dynamics | holds: equal shares by Schmidt, gravity to first order by the first law of entanglement | Faulkner, Guica, Hartman, Myers and Van Raamsdonk 2014 | isolation and local verification (the branch) |
| 0g where to push | the maintained equilibrium: Jacobson 2016 past first order, the threshold theorem for the budget | Jacobson 2016; Aharonov and Ben-Or 1997 | nothing yet; one question for a physicist |
| 0h entanglement defined by paths | fails as a definition (Werner, swapping), holds as the hypothesis that the field is quantum | LOCC theorem; Bose et al. 2017; Marletto and Vedral 2017 | the word definition for the word hypothesis |
| 0i the second definition | holds; a theorem for pure states (Gisin 1991), too strict for mixed (Werner 1989) | Fine 1982; Gisin 1991; the no-communication theorem | nothing; DMP refuses what the quantum entangles |
| 0j Zeno | contradiction: live verification freezes the quantum; resolved by restricting the information half to declared expectations | Misra and Sudarshan 1977; Pallister, Linden and Montanaro 2018 | the open truth check of the information half |
| 0j' monogamy | contradiction: a hierarchy of maximally entangled pairs cannot exist; resolved by the majority form | Coffman, Kundu and Wootters 2000 | the pair for the perfect tensor, on the quantum side |
| 0k authorisation downward | holds: causal set theory, order plus number is geometry; predicts Λ ~ 1/√N | Malament 1977; Bombelli, Lee, Meyer and Sorkin 1987; Rideout and Sorkin 2000 | nothing; the quantum dynamics is open |
| 0l truth as existence | holds: closes Zeno (membership commutes with content), closes the converse; lands on the constraint picture | Tarski 1933; Dirac 1964; DeWitt 1967 | nothing; the next freeze is the problem of time, resolved by an internal clock (Page and Wootters 1983) |
| 0m constants at G0 | right: configuration at the minting (about twenty-seven, not three) and unitarity; not the dynamics | Planck 1899; Smolin 1992 | nothing; the law is still unnamed |
| 0n inflation as radiation | hypothesis: the horizon does radiate, the fast start is Vilenkin's, the smoothness is Penrose's; wrong in order, no tilt | Planck 2018 n_s; Kofman, Linde and Starobinsky 1994 | the word explain |
| 1 field | fails as "vector", holds as "frame" | Weinberg 1964; Deser 1970; the tetrad | the word vector for the word frame |
| 2 dynamics | holds, classical | Lovelock 1971; Jacobson 1995 | nothing; G and Λ stay inputs |
| 3 quantum | **fails: the fork** | Bell 1964; Tsirelson 1980; Kochen and Specker 1967 | isolation (then it is purification, published) or the quantum (then it is DMP) |
| 4 discreteness | fails, no spectrum | Rovelli and Smolin 1995; Meissner 2004 | nothing can be given up; a counting must be added |
| 5 measure | fails, support not measure | Gleason 1957 | needs level 3 first |
| 6 cosmology | fails, no number | Li 2004; the acceleration at redshift 0.6 | nothing can be given up; Λ is an input |
| 7 horizon | holds as shape, no area bound | Bekenstein 1981 (both bounds) | T38, every layer its own Duality; not given up |

## 4. What is useful

**For physics: nothing new, one honest sentence.** The approach the owner intends is the join of two published programmes, thermodynamic
gravity (Jacobson 1995 and after) and the informational reconstruction of quantum theory (Chiribella, D'Ariano and Perinotti 2011 and
after). Each is sound, each reaches its classical or its quantum half, and each stops at the same step: the microscopic degrees of freedom
that would make the join a quantum gravity. The axiom system adds no postulate to either side. A physicist needs nothing from it, and this
pass poses no question to one.

**For DMP: three definitions came back sharper, as the owner's method predicts.** Each is a candidate for his approval, none changes text
here.

1. **The hierarchy is a theorem, not an axiom.** The owner's corrected ninth sentence, "the lowest total leakage of all information across
   that number of dualities arranged in any possible order", counted as the standings that cross each Duality's boundary (the spin-network
   reading), is the sum of degrees of the arrangement's graph, 2·|E| (Euler 1736, the handshake lemma). The least leakage at which every
   item is still reachable from any other is a connected graph with the fewest edges, which is a spanning tree with N − 1 edges, and no
   non-tree does better (a connected graph on N vertices has at least N − 1 edges, with equality exactly for trees). So "information is
   hierarchical" (Axiom 3) follows from least leakage plus reachability; the median layout of Axiom 3 then picks which tree. The two
   optima the brief asked about are nested, not rival: leakage fixes the family, demand fixes the member. The number the owner asked for
   (02:50Z) is the mean leakage per Duality in that family, 2 − 2/N: approached as N grows, never attained, with zero leakage being T37's
   collapse where nothing is reachable. That is where the owner's 2 lives: the mean degree of a tree, not its fan-out. **Refuter:** an
   arrangement in which every item is reachable, with fewer than N − 1 standings; graph theory says there is none. A tree's fragility is
   not an objection, since DMP pays for it inside the node (three nodes per half, T8a) and not in the graph.
2. **Axiom 1's balance has a number, and it is per minting, not universal.** The trust half contracts (fewest hops, the star); the
   information half pushes back (two live checks per child per window); the equilibrium is the fan-out b* = ⌊(r·W − L) / 2⌋ of
   gravity#17 section 2, a corner solution with no constant at 2, e or 3.59. The Chandrasekhar shape holds (attraction against a
   pressure, a limit with a number), and the number is the minting's r and W, as the Chandrasekhar mass is ħ, c, G and the proton mass.
   **Refuter:** the benchmark of gravity#17 section 2 giving anything but a line of slope −1/2.
3. **The boundary is a rate bound, not a content bound** (level 7). Say it in DMP's words and the holography claims in the brief stop
   overreaching: DMP's Bekenstein is the channel bound, not the area bound. **Refuter:** an instance whose interior count is bounded by
   its root budget; T38 forbids it.

## 5. The open drafts, one line each

- **gravity#17** (physics.md, qg-attempt.md, seven NoGo files, findings F11 to F26): the Lean stands and is cited above by name; the two
  prose files say what this file says in 620 lines, and this file replaces them as the reading text if the owner prefers it; the
  benchmark card and B1 to B6 stand, B4 is superseded by item 1 of section 4.
- **dmp#24** (theorem pass, renumbering, constraints restated, two-axiom brief): the two-axiom brief's four refuters are right and the
  recommendation (three axioms for this pass) stands; level 3 above adds the fifth refuter, the fork, which the brief's "QG is conjecture"
  line only gestures at. The renumbering is the owner's call and is not a physics question.
- **dmp#22** (Z code round 1): the three highs are real and none is a hole in DMP; the verdict in dmp#24's `zcode-round1-verdict.md` is
  right and needs nothing from this pass.
- **dmp#20 and gravity#14** (exclusion and inclusion by voting share): not a physics question; untouched by this pass.
- **The IM rename to "DEP":** the owner's naming decision; parked.

Status: draft for the owner. Nothing in it changes DMP; the three items of section 4 are candidates for his "approved".
