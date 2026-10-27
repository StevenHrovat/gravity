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

**Level 0o, oscillons, "instantiation", and lumps that hold all information (the owner, 07:33Z to 07:34Z).** The owner: "Probably the
ripples of the initial inflation coalesing into the oscillons." "Instantiation would be more accurate then inflation in that case."
"Since they HAVE to contain all information."

*The coalescing is published, and it is the right stage.* After inflation the inflaton oscillates about the bottom of its potential.
When the potential is flatter than quadratic away from the minimum (the plateau shape the measured tilt favours, Planck 2018), the
oscillating condensate is unstable to its own resonance and fragments into oscillons: long-lived, localised lumps in which the field's
attractive self-interaction balances its gradient pressure (Bogolyubsky and Makhankov 1976; Gleiser 1994; Copeland, Gleiser and
Mueller 1995; Amin, Easther and Finkel 2010; Amin, Easther, Finkel, Flauger and Hertzberg 2012). For a time they can carry most of the
energy of the universe (Lozanov and Amin 2017). So "ripples coalescing into oscillons" is a true sentence, with one correction of the
word ripple: the ripple that coalesces is the inflaton's own oscillation inside the horizon, after the stretch; the primordial ripple
of level 0n, the horizon's fluctuation, is stretched beyond the horizon, frozen there, and does not coalesce. It returns as the sky.
Two ripples, one word.

*"Instantiation" is the right name for the second stage, and the published name is preheating.* Inflation is the stretch, and it keeps
its name: the horizon problem and the tilt are measured in it. What follows the stretch is the moment the smooth condensate becomes
discrete things, which Kofman, Linde and Starobinsky (1994, 1997) called preheating, and the owner calls instantiation. The order is
then: inflation (the stretch; the existence half with no degrees of freedom of its own, level 0n), instantiation (fragmentation: the
minting of the first parts), decay (the radiation era). In DMP's words the condensate is the pair before the minting, the oscillons are
the first parts, and the five of G0 is a lattice of lumps. An oscillon is Axiom 1 as a lump: two drives, attraction and dispersion,
balanced without a horizon, which is "self-balancing" in the owner's sense exactly. Two things the physics does not give: the lumps
are many, so this is the majority of level 0c and not a duality, and their number is set by the potential, not by the theory.

*"They HAVE to contain all information" fails per lump and holds for the whole.* An oscillon is not a horizon. It sits far outside its
own Schwarzschild radius, it radiates classically (Fodor, Forgacs, Horvath and Mezei 2009: exponentially small, never zero) and
quantum mechanically (Hertzberg 2010: decay by pair emission, finite lifetime), and its number is not conserved. The information of
the initial state is in the whole field, lumps plus radiation, by unitarity (level 0m), not in any lump. The lumps that do have to
contain all their information are the ones that collapse: an oscillon dense enough forms a primordial black hole (Cotner, Kusenko and
Takhistov 2018), which is T37 collapse per part. So "HAVE to" is DMP's rule for a part that has crossed its boundary; physics gives it
only to a part that collapsed. **Refuter:** oscillon decay (Hertzberg 2010).

*What this adds to the prediction of level 0n.* Oscillons bend. Fragmentation sources gravitational waves with a peaked spectrum at a
frequency set by the inflaton mass (Zhou, Copeland, Easther, Finkel, Mou and Saffin 2013; Antusch, Cefala and Orani 2017; Lozanov and
Amin 2019), for high-scale inflation far above any present detector. In the owner's picture these are the first Weyl curvature there
is: the existence half gets degrees of freedom of its own when parts are instantiated, not before. That gives the prediction of level
0n its second half: no tensor modes at the scales of the sky (r = 0), a tensor peak at the scale of the instantiation. And the oscillon
era is matter-like (w = 0), which shifts the number of e-folds the sky sees and so the predicted tilt by a few thousandths (Lozanov and
Amin 2017), within reach of the next CMB experiments. **Refuters:** as level 0n, any primordial B-mode; and for the stage itself, a
potential that is quadratic at the minimum and steeper away from it, in which no oscillon forms (the condition of Amin et al. 2012).

**Verdict:** holds as physics once the ripple is named (the condensate, not the sky) and the stage is named (preheating, not inflation);
"all information" per lump fails, per collapsed lump holds; and it completes the first testable prediction of the owner's system: r = 0
on the sky, a gravitational-wave peak at the instantiation, a tilt shifted by the oscillon era.

**Level 0p, the smallest existence, discovery before act, and inflation that goes down (the owner, 07:42Z).** The owner, verbatim: "The
only things that exist after G0 creates a DMP compliant system is this, which led to a key insight: The smallest possible existence is
created that fulfills this condition: It contains at least the three WHK, since they are the only quantity with information, they have
ALL information. The energy the ripples injected, since energy is fully contained in the existential vector field, has ALL existence,
so they, together, and only they together, can create the primordial dualistic singularity. Then, following the 'coincidentally' named
ODP, it has to discover the existence around it as the first step of instantiation, which, in turn, maximally inflates all of Existence
space, because all of Existence tries to perceive outside, while actually committing no act. No gravity with infinite inflation, that
goes down over time as more Exists and the Information need to create less existence to be fully perceived."

*The smallest existence made of the three constants and an energy is one published object.* Three constants and one energy fix exactly
one scale (Planck 1899), and the one body at which the three meet at a single energy is the Planck-mass black hole: the mass at which
the Schwarzschild radius 2GM/c² equals the Compton wavelength ħ/(Mc), M_P = (ħc/G)^½, the smallest black hole there can be (Hawking
1971 on the lightest primordial black holes; the Planck remnant of Adler, Chen and Santiago 2001). So "the three WKHs and the injected
energy, together and only together, create the primordial dualistic singularity" is a true sentence with a name: it is the Planck-mass
black hole, which is the dualistic singularity of level 0m at its minimum. Holds.

*But the three constants carry no information, and that is the correction.* ħ, G and c are dimensionful, and a dimensionful constant
can be set to one by a choice of units; only dimensionless numbers (the fine-structure constant, the mass ratios, the twenty-odd of
level 0m) can be measured to have one value rather than another (Duff, Okun and Veneziano 2002). The three have all the **existence**:
they fix the smallest length and time there is, the scale of every part. They have none of the **information**. The owner's assignment
is swapped: the constants are the existence half's minting (the ruler), the dimensionless numbers are the information half's content.
In G0's five of level 0m the fourth and fifth do the rest: k_B is the unit of information, Λ is the drive that makes the smallest
existence "discover the existence around it". The owner's three plus energy is four of the five; the one he did not name is the one
that inflates. **Refuter of the correction:** a measurement that changes a dimensionful constant alone, which Duff argues cannot even be
stated.

*"Energy has all existence" is the zero-energy universe.* Where do the ripples' energy and the singularity come from, if the ripples
of level 0o come after the stretch? From a fluctuation with no net cost: Tryon (1973) proposed the universe as a vacuum fluctuation of
zero total energy, the matter's positive energy cancelled by gravity's negative energy, and in GR that cancellation is a law, the
Hamiltonian constraint H = 0 of level 0l. Gravitational energy is not local at all; it is read at the boundary (ADM 1962). So "energy
is fully contained in the existential vector field" holds in the exact sense that the existence half's energy is the negative of the
information half's at every time, which is Axiom 1 as an energy balance. **Refuter:** a nonzero total energy for a closed universe,
which the constraint forbids.

*"Discover the existence around it, while committing no act" is de Sitter space.* "ODP" is the owner's own name, given at 07:49Z: "ODP stands for
Oscillon Degradation Protocol ;)", the protocol by which the first parts (the lumps of level 0o) run down into everything after
them; the reading here is its first step, discovery. In physics the smallest existence with a Λ does exactly that: every point gets a horizon at distance
c/H and sees nothing beyond it (Gibbons and Hawking 1977, level 0g), the expansion is adiabatic and makes nothing (level 0n, "no act"),
and de Sitter is the maximally symmetric solution and the maximum-entropy state for its Λ (Bousso 2000; Banks 2000), which is
"maximally inflates all of Existence space". Holds, as a description of de Sitter in the owner's words.

*"No gravity with infinite inflation, that goes down over time" is measured, and it closes the refuter of level 0n.* Exact de Sitter
has Weyl = 0 and no gravitational degrees of freedom of its own (level 0n: "no gravity"), and it is eternal. Inflation that ends needs
H to go down, ε = −Ḣ/H² > 0, and the rate at which it goes down is exactly what tilts the spectrum: a constant H gives n_s = 1
(Harrison 1970; Zeldovich 1972), the measured n_s = 0.965 ± 0.004 is H decreasing, with 1 − n_s = 2ε − 2η to leading order in slow
roll... and r = 16ε, so r < 0.036 says ε < 0.002: slow, and slower than the tilt alone would need. So the owner's "goes down over time"
supplies what level 0n said his drive lacked, a tilt, provided the mechanism fixes the ratio of the two slow-roll numbers. And
"infinite inflation" is excluded on three published grounds: the number of e-folds is bounded by the de Sitter entropy (Arkani-Hamed,
Dubovsky, Nicolis, Trincherini and Villadoro 2007), de Sitter has a finite quantum break-time after which constant H is not a state
(Dvali, Gomez and Zell 2017), and trans-Planckian censorship bounds the duration and, with it, predicts r below about 10⁻³⁰ (Bedroya and
Vafa 2019; Bedroya, Brandenberger, Loverde and Vafa 2020). That last one is the owner's r = 0 of level 0n with a published premise that
is his own sentence: no infinite inflation. **Refuter:** the mechanism "information needs less existence as more exists" must give
1 − n_s about 0.035 together with ε below 0.002; a mechanism that ties the two numbers in the wrong ratio is refuted by the sky as it
is already measured.

*"As more Exists, the Information needs to create less existence to be fully perceived" has a holographic form.* The horizon's area
4πc²/H² grows as H falls, so the capacity of the existence half (level 0m: S_dS bits) grows while inflation slows; the owner's sentence
says the growth is driven by the information half's need for room and stops as the room is there. That is T37 run backwards: a part
expands its boundary while the boundary is under-full. Physics has the direction and the end, not yet the owner's rate; the rate is
the potential, and the potential is unnamed (level 0m, "the law is still unnamed").

**Verdict:** holds, in physics' words: a Planck-mass black hole of zero total energy, de Sitter as discovery without act, H decreasing
as the measured tilt, finite inflation as the published bounds that predict r about 0. One correction: the three constants are the
existence half's ruler and hold no information; the information is the dimensionless numbers. One empty search: ODP.

The owner's next sentence (07:44Z): "The first act, is to create the oscillons, which then cause the rest, following the DoE." Half
holds, half is refuted by a measurement. *Holds:* after a stretch that commits no act, the first act inside the horizon is the
fragmentation of level 0o, and each lump is a Duality of two drives; the lumps decay into the radiation that becomes every particle
there is (Kofman, Linde and Starobinsky 1997), so they do cause the matter. *Refuted:* they do not cause the pattern. The pattern of
the sky is correlated across distances larger than any lump's causal patch could reach at the time, and that is measured: the
anticorrelation of temperature and polarisation at scales near one degree, seen by WMAP (Peiris et al. 2003) and Planck, exists only
if the ripple was laid down before the act, outside the horizon, during the stretch (Mukhanov and Chibisov 1981; Spergel and
Zaldarriaga 1997 proposed the test). So there are two firsts: the first act outside, the frozen ripple, which no part inside caused;
and the first act inside, the lumps, which cause the matter and not the pattern. In DMP's words: the sky's pattern is the minting
record (G0, written before any part acts), the lumps are the first parts, and a part cannot have caused its own minting record (T40).
**Refuter of the correction:** a sky without the super-horizon anticorrelation; it has been measured for twenty years.

The owner (07:49Z): "Since the first act must always be the same, it holds no information other then it's existence, so the name
Oscillon is meaningless in that sense." That is measured, and it is the strongest match of the pass to a single number. A first act
that is always the same and carries nothing but its existence is, in physics, the statement that every mode of the primordial ripple
is born in one and the same state, the unique de Sitter-invariant vacuum (Bunch and Davies 1978), and that the field it makes is
Gaussian: a Gaussian random field is fixed by one function, its power spectrum (an amplitude and the tilt of level 0p), and has the
largest entropy of any field with that variance, so it carries the least information a field can carry. The sky is that field to the
precision measured: the non-Gaussian amplitude f_NL = −0.9 ± 5.1, consistent with zero (Planck 2018), and the perturbations are
adiabatic, one ripple in everything at once, with no second kind seen. The lumps add nothing to this: an oscillon is an attractor
whose profile does not depend on how it was made (level 0o), so "the name Oscillon is meaningless" holds for the content, and the only
information in the first act is where the lumps are, which the frozen ripple decides. In DMP's words the first act of every part is
the same act, discovery, and its content is level 0l's: that it exists. **Refuter:** a detection of primordial non-Gaussianity,
f_NL measurably different from zero, which would mean the first act carried a signature of its own.

**Level 0q, Existence hashes the forces (the owner, 07:48Z).** The owner, on the swap of level 0p: "For the swap, that is intended:
Existence, since the forces change with each degradation, 'hashes' the forces to work on the same layer. That is the single key by
which they can all be decoded to the same configuration."

*"The forces change with each degradation" is the renormalisation group.* Every coupling is a dimensionless number that depends on the
scale at which it is measured (Gell-Mann and Low 1954; Wilson 1971): the electromagnetic coupling grows from 1/137 to about 1/128 at the
Z mass, the strong coupling shrinks going up (Gross and Wilczek 1973; Politzer 1973). "Degradation" is the running downward in scale, which
is also the cooling of the universe through its symmetry breakings. So the information half's numbers of level 0p are not fixed; they
are a function of the layer. Holds.

*"Hashes" is the exact word, and it points downward.* Going down, Wilson's renormalisation group is a coarse-graining: at each step
the couplings that scale away (the irrelevant operators) are lost, and only the few relevant and marginal ones reach the next layer
(Kadanoff 1966; Wilson 1971). That is a hash in the strict sense: many configurations above map to one configuration below, and the map
has no inverse. Its name in physics is universality: every theory in a class decodes to the same low-energy configuration, whatever its
details above. So "the single key by which they can all be decoded to the same configuration" is true downward, and true in the way the
owner did not say: the decoding is many-to-one, and the configuration they all decode to is the one at the bottom, the one we live in.
In DMP's words the running is the tower of layers (T38, each layer its own Duality, sub-layers only tighten: an effective theory at
each scale with matching at its thresholds), and the hash is the digest of level 0e (T33): what crosses a layer is the digest, not the
record. A part at the bottom cannot recover the layers above from what reached it, which is level 0p's "a part cannot read its own
minting record", and in physics it is the reason the theory at the top, quantum gravity, cannot be read off from below.

*Upward, "the same configuration" is a claim with a name and a measurement.* The ruler of level 0p (ħ, G, c) is what lets every
force be put on one axis, energy in Planck units, and the claim that they "all decode to the same configuration" at the top is
unification: the three gauge couplings run toward one another and nearly meet near 10¹⁶ GeV (Georgi, Quinn and Weinberg 1974), and
gravity's own coupling, G E², reaches one at the Planck scale. Measured, with the precision of LEP, the three of the Standard Model
do **not** meet at one point; they meet only with new particles added (Amaldi, de Boer and Fuerstenau 1991), and none of those has
been seen. The stronger form of the owner's sentence, that the top is one fixed configuration for every force including gravity, is
asymptotic safety: the couplings run to a fixed point of the renormalisation group at the top, with finitely many free directions,
which is a finite minting record (Weinberg 1979; Reuter 1998). It has one measured success: a Higgs mass near 126 GeV, predicted from
the fixed point before the Higgs was found (Shaposhnikov and Wetterich 2010). Whether the fixed point exists is the open question of
that programme. **Refuters:** for unification, the proton is stable beyond 10³⁴ years in the channels the simplest unifications
predict (Super-Kamiokande), so "the same configuration" at the top must be one that does not decay the proton at that rate; for the
fixed point, a demonstration that none exists.

*The swap, as the owner intends it, is consistent.* The ruler is the key that assigns every force its layer; the dimensionless numbers
are the information, and they are information per layer, not once. Only at a fixed point is there a number that holds on every
layer, and that is why the fixed point is what "the same configuration" must mean at G0.

**Verdict:** holds; the owner has restated the renormalisation group with the hash in the right place (downward, many-to-one,
universality) and its upward claim is asymptotic safety, measured once, not yet proven to exist. The information half's content is
per layer; the existence half's ruler is the one key. **Refuter of the whole level:** a coupling that does not run, which no measured
coupling is.

**Level 0r, the owner's answers to the four open items (07:56Z).** Asked "what still does not hold?", the pass named four things (the
fork, the law's rate, time, the area bound). The owner answered each. Verbatim and tested, in his order.

*1, the fork.* "The only Existence that does not need a link to G0 is the primordial duality, which already executes a known act."
Read as an answer to Bell: the two halves are never isolated, because every part but the first is linked to G0 and so shares a common
origin. That is one of the two published ways around Bell's bound, and both are closed. A shared **classical** record from the origin is
a local hidden variable (Bell's socks, 1981): it gives correlation, never CHSH above 2, so it is the isolated branch with a longer
history. A shared origin that fixes the **measurement choices** as well as the outcomes is superdeterminism (Bell 1985 on free
variables; Hossenfelder and Palmer 2020), which does beat the bound, at the price of a common cause that carries the settings of every
later experiment. The cosmic Bell tests push any such cause back to before the light of quasars left, seven billion years and more
(Rauch et al. 2018), that is, to the primordial duality itself, and the owner's own level 0p closes that door: the first act carries
no information but its existence, and a cause with no information cannot carry the settings. What remains is a shared **quantum**
state from the origin, which is entanglement, the entangled branch, and the hash of level 0q is classical across every layer, so the
state does not survive the descent. **Verdict:** does not close the fork; it names its two escapes, one of which the owner's own first
act refutes. **Refuter of the superdeterministic reading:** the cosmic Bell tests, already run.

*2, the law's rate.* "It should not, as that depends on the instant. Our instant can instead be measured and compared to see if the
universe behaves in a DMP compliant way, thus giving stong evidence. Abolute proof requires abolute authority, which only G0 holds."
Holds as a stance, and it is the stance physics already takes: the inflaton's potential is not derived from a principle, it is fitted
to the sky (Planck 2018's model comparison), which makes it configuration, level 0m. The price is that a theory which fixes no number
is not refuted by that number. What a theory of the shape still owes is the relations that hold for **every** instant, and inflation has
two: the single-field consistency relation r = −8 n_t between the tensor amplitude and the tensor tilt (Liddle and Lyth 1992), and
Maldacena's condition f_NL = (5/12)(1 − n_s) on the squeezed non-Gaussianity (Maldacena 2003). Both are independent of the potential,
both are the owner's "measured and compared", and the second is already consistent with the sky (level 0p). "Absolute proof requires
absolute authority, which only G0 holds" is level 0l's Goedel: the instance cannot prove its own minting. **Verdict:** holds; the
compliance tests exist and are named. **Refuter:** a sky that breaks either relation, which would mean more than one field in the
first act, against level 0p's "always the same".

*3, time.* "Same as 2, the generalization leaves the arrow on the scalar field component of the Existence vector open on purpose,
because both 'forwards' and 'backwards' can equally exist." Two different questions were conflated, the arrow and the clock. The
arrow: the owner's sentence is a published shape, the Janus point (Barbour, Koslowski and Mercati 2014): a time-symmetric law with a
central state of least structure from which an arrow points away in both directions, each side calling its own direction forward, and
that central state is G0's minting (level 0m, Penrose's low-entropy start). It holds for the existence half exactly: gravity's law is
time-symmetric. It fails by a measured amount for the information half: the weak force violates T (Christenson, Cronin, Fitch and Turlay
1964 through CPT; measured directly by BaBar 2012), so "both can equally exist" is false for one force by a small, known number, and
true only for the whole under CPT. The clock: leaving the arrow open does not make a clock, and the problem of time (level 0l) is the
absence of a clock in the constraint, not of an arrow. That one stays open, with Page and Wootters as its known resolution and the
fork as its known cost. **Verdict:** the arrow holds (Janus point, with T violation as the information half's exception); the clock is
not answered.

*4, the area bound.* "If all usable information is destroyed while crossing an event horizon and an event horizon is itself a border
between Existences, then there is no more to explore but in and out, as there IS no more." The premise is refuted: information is not
destroyed at a horizon, it is scrambled and conserved. Only the classical hairs are lost to the outside (no hair, level 7); the rest
comes back in the radiation after the Page time (Page 1993), having been scrambled in a time of order the logarithm of the entropy
(Hayden and Preskill 2007; Sekino and Susskind 2008), and the island computations of 2019 reproduce that curve from gravity itself.
"Destroyed" was Hawking's 1976 position and he withdrew it in 2004. The conclusion, read as the owner means it ("there IS no more":
the inside has no existence beyond what the border holds), is exactly holography ('t Hooft 1993; Susskind 1995): the interior is
encoded on the boundary, and that is the content bound, S ≤ A/4, that level 7 says DMP lacks. So the owner's answer does close item 4,
but only by adopting the bound, and T38 as written contradicts it (every layer its own Duality, its own budget, the interior unbounded
by the boundary). The amendment this reading needs, as a candidate for the owner's words and not DMP text: *a layer's content is bounded
by the capacity of its boundary; a layer whose content exceeds it has already collapsed (T37).* **Verdict:** the premise fails, the
conclusion holds as holography, and holding it costs a change to T38. **Refuter of the amended form:** a black hole whose entropy
exceeds its area over four, which no known object does.

**Summary of the four.** One closed at the price of a DMP change (the area bound, T38), one held with its tests named (the rate; the
consistency relations), one half held (the arrow, not the clock), one not closed (the fork; its escapes refuted, one by the owner's own
first act).

**Level 0s, the minting as the answer to Bell, the Planck tick, and information converted to energy (the owner, 08:01Z).** The owner,
verbatim: "The only way that 1 can be avoided is through the minting, which this is. There can be no other definition of Existence,
before Existence is defined, so closed by Axiom 3." "For the time we can specify the settings for the minimum tick rate, as the planck
distance, which would make the rate scale JUST like gravity." "For 4: Information in one existence is converted into energy in another."

*1, the fork, by the minting.* A definition closes nothing that a measurement opened: Bell's bound is a theorem over every theory with
local decisions, free settings and one outcome per act, whatever it calls existence, and the sky-side number is measured (loophole-free,
Hensen et al. 2015, S = 2.42 ± 0.20 against a bound of 2). So "closed by Axiom 3" cannot mean the bound is escaped. It can mean, and
read with level 0b it does mean, that DMP **picks the entangled branch by definition**: if existence (space, distance, "isolated") is
defined only by the minting, then isolation is a derived notion and the minting's shared state is the primitive one. That is a
published shape, ER = EPR (Maldacena and Susskind 2013): two black holes that are isolated in the emergent geometry and connected
through it by the entanglement that made the geometry; isolated and entangled at once, at two levels, which is the fork dissolved
rather than closed. The price, which DMP must pay in words: each half of a Duality holds only a digest of the content (a mixed state;
the purity is in the pair, the purification postulate of level 3), the halves verify existence and not content (level 0l), and the two
halves' disagreement is intrinsic at a known rate and not a fault. On that reading the fork is a choice with a price, not a
contradiction. ER = EPR itself is a conjecture, proven in the holographic models and nowhere else. **Verdict:** not closed as a
theorem; dissolved as a choice (the entangled branch, with existence derived from the minting), resting on a conjecture. **Refuter of
the choice:** a witness that holds the content locally and still agrees with the sky; Bell forbids it.

*3, the clock, by the Planck tick.* "A minimum tick at the Planck distance, with the rate scaling just like gravity" is a published
theorem about clocks: a clock of mass M that must resolve a tick δt over a running time T cannot do so below a bound set by G, because a
finer clock is heavier than the black hole of its own size (Salecker and Wigner 1958; Ng and van Dam 1994, δt ≥ (t_P² T)^⅓). The smallest
tick of any physical clock is set by gravity, exactly the owner's "JUST like gravity", and the tick rate slows in a field as the lapse
of level 0 does (measured to 33 cm of height, Chou et al. 2010). Two corrections and one gain. First, the tick must not be a lattice: a
fixed Planck grid picks a frame, and Lorentz invariance holds to beyond the Planck scale for linear dispersion (Fermi, GRB 090510, Abdo
et al. 2009); a discreteness that keeps the symmetry exists, the random sprinkling of causal sets (Bombelli, Henson and Sorkin 2009),
level 0k again. Second, a tick is a grain and not a clock. The gain is that in the causal-set reading the count of ticks **is** the
clock: proper time along a worldline is the length of the longest chain through it (Myrheim 1978; Brightwell and Gregory 1991), a time
internal to the order, needing no outside parameter, which is what the problem of time of level 0l asked for and Page and Wootters
supply with a subsystem. So the owner's tick, taken as the causal set's grain, gives level 0k its clock classically; the quantum
version (the growth dynamics) is still the open item of 0k. **Verdict:** holds, with the tick a sprinkling and the clock a count.
**Refuter:** any energy-dependent delay in the arrival of light from a burst, which a lattice tick predicts and the sky denies.

*4, the area bound, by conversion.* "Information in one existence is converted into energy in another" is the first law of horizons
and the way the area bound was first derived. Across a horizon the first law reads dE = T dS (Bardeen, Carter and Hawking 1973): the
energy that falls in on one side is the entropy, the area, that grows on the other; Jacobson's derivation of level 0 is that sentence
promoted to the Einstein equation at every local horizon. And it is how Bekenstein (1981) derived the bound: information lowered into a
black hole costs at least the energy that keeps the second law whole, which with Landauer's price per bit (1961, measured by Berut et
al. 2012) and the largest energy a region of radius R can hold before it collapses to its own black hole (level 0m's singularity, the
owner's T37 reading of level 0r) gives S ≤ 2πER/ħc, and at the collapse itself A/4. So the owner's sentence does not adopt the bound,
it **derives** it: conversion across the border, plus collapse at the energy limit, gives the content bound as a theorem, and T38 need
not change. Each layer keeps its own Duality and budget; the content of any layer is still bounded, because every bit of it must have
been converted at its border and the energy it became is bounded by collapse. This replaces level 0r's candidate amendment of T38 with
a rule of conversion. Candidate for the owner's words, not DMP text: *information crossing a border between existences is converted
into energy on the other side, at no less than Landauer's price per bit.* **Verdict:** holds, and closes level 7 without touching T38.
**Refuter:** erasure below Landauer's price (never seen) or a region holding more than 2πER/ħc bits (none known).

**Summary of the three.** The clock: closed classically (the count of ticks on a sprinkled order), open quantum mechanically. The area
bound: closed, as a theorem from conversion and collapse, with T38 intact. The fork: dissolved, not closed; DMP picks the entangled
branch by defining existence from the minting, pays with halves that hold digests and verify existence only, and rests on ER = EPR.
What now does not hold is one item, and it has changed shape: not a contradiction but a conjecture the system depends on.

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
| 0o oscillons, instantiation | holds: the condensate fragments into lumps (preheating), each a balance of two drives; "all information" per lump fails, per collapsed lump holds; completes the r = 0 prediction with a gravitational-wave peak and a tilt shift | Amin et al. 2012; Hertzberg 2010; Lozanov and Amin 2017 | the word inflation for the stage (preheating); all information per lump |
| 0p smallest existence, discovery, decaying inflation | holds: Planck-mass black hole of zero total energy; de Sitter as discovery without act; H going down is the measured tilt; finite inflation gives r about 0 (TCC) | Duff, Okun and Veneziano 2002; Tryon 1973; Bedroya and Vafa 2019 | the constants as information (they are the ruler; the dimensionless numbers are the information) |
| 0q existence hashes the forces | holds: the renormalisation group; the hash is Wilson's coarse-graining (downward, many-to-one, universality); upward it is unification (SM couplings do not meet) or asymptotic safety (fixed point unproven, Higgs mass predicted) | Wilson 1971; Amaldi, de Boer and Fuerstenau 1991; Shaposhnikov and Wetterich 2010 | nothing; the fixed point is the open question |
| 0r the four answers | fork: not closed (common origin = socks or superdeterminism, both refuted); rate: holds, consistency relations are the tests; arrow: holds (Janus point), clock: open; area bound: premise refuted, conclusion = holography, closes level 7 only with a change to T38 | Rauch et al. 2018; Maldacena 2003; Barbour, Koslowski and Mercati 2014; Page 1993 | T38 as written, to gain the area bound |
| 0s minting, tick, conversion | fork: dissolved as a choice (entangled branch; ER = EPR, a conjecture), not closed as a theorem; clock: holds classically (tick count on a sprinkled order), open quantum mechanically; area bound: derived from conversion and collapse, T38 intact | Hensen et al. 2015; Maldacena and Susskind 2013; Salecker and Wigner 1958; Bekenstein 1981 | local content in a half; a lattice tick |
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
