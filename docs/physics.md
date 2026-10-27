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
