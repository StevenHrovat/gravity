# Physics and information theory: what DMP says back, and what it does not

Part 0 of the verifying session (DMP `docs/proposals/c-constraints.md`, sections 4.1 and 4.2; the owner, 2026-10-27 01:29Z: "try the
physics and information theory stuff first ... push the bounds with it and distill the interesting stuff that falls out into something
actually useful and coherent"). The rule of the pass: cite what has stood the test of time, say where DMP's object differs, prove only
that difference, and in Lean only where the field theorems already carry it. Every kept item names the result that would refute it;
every dropped item gets one line. Nothing here changes DMP; it is the owner's reading queue. The one piece of Lean the pass needed is
`evidence/Dmp/Physics.lean` (the capacity bound, the content-free readout).

**The verdict in one paragraph.** The owner's picture holds as a map and fails as a mechanism in two places, and both failures are useful.
It holds: DMP's horizon, floor, no-hair readout, second law, censorship, covariance and erasure each sit on a settled result and each has a
theorem in the evidence chain (section 1). It fails, first, on what holds the horizon open: in GR nothing does (a horizon is a causal
surface; pressureless collapse forms one before the singularity, Oppenheimer and Snyder 1939), while in DMP something must, and it has a
number: the Duality's budget of live checks per validity window (section 2, `Schedule.some_standing_lapses`). It fails, second, on the
fan-out: no DMP cost model lands at 2 or at e; the information tree's fan-out is the budget, and the 2 is the trust tree's by definition
(a part is two halves, the words), so the prediction is a definition on one tree and falls on the other (section 2). What DMP says back
to physics is nothing a physicist needs (section 5): the one open question it touches, the end state of evaporation, DMP answers by
construction (destroy before the cipher dies, T31), which is Hawking's 1976 answer, rejected in physics for reasons that rest on energy
conservation, which DMP has not.

## 1. What holds: the map

| Settled result | DMP object | Lean | Where DMP differs |
|---|---|---|---|
| The horizon as a one-way boundary (Penrose 1965; Hawking and Ellis 1973) | containment (the words), the trap (T31) | `Floor.road_gate` | held by live verification (Axiom 2), not by causal structure: it needs work to stay a horizon |
| No hair: the outside sees mass, spin, charge and nothing else (Israel 1967, Carter 1971, Robinson 1975) | T31's readout: size, staleness, rotation interval; T32's temperature | `Entry.ext` (Physics.lean): an entry is its time and three verdicts, nothing else | the hairs are a listed set, proven by the type |
| The area theorem and the second law (Hawking 1971; Bekenstein 1973) | the record only grows under the system's own acts; the perimeter shrinks on one witness, grows only with two (T24) | `Record.run_records_all`, `Standing.one_witness_never_loosens`, `Field.k4_refresh_never_raises` | one exception physics has not: a two-witness destruction at the legal date (Axiom 3, T27) |
| Hawking radiation, thermal (1975) | the entropy floor: what leaves is random bytes of the same length (T31) | `Floor.road_evidence` | the emission never carries content: no paradox, only a retention date |
| Weak cosmic censorship (Penrose 1969) | a minted pair never exposes under one cause; the pressed instance is the naked singularity (T-P) | `DoT.confined_influence_never_passes_alone`, `DoT.not_minted_collapses`, `Ground.pressed_collapse` | a theorem for minted pairs, false for pressed ones; in GR a conjecture about formation |
| Fast scrambling, logarithmic in the entropy (Sekino and Susskind 2008) | a layer heals in depth + 1 rounds (Dolev, Israeli and Moran 1993) | `R2Stable.st_self_stabilizing` | the same logarithm (a tree's depth) from another mechanism; DMP's inside is placed (`ms_one_layout`), placeless only from outside |
| Landauer: erasure costs at least kT ln 2 per bit (1961) | a destruction is a recorded two-witness act: content goes, existence stays (Axiom 3) | `Floor.road_record`, `Floor.destroyed_stays`, `Record.step_records_once` | erasure costs one entry and two signatures, never nothing |
| Degeneracy pressure against gravity (Chandrasekhar 1931; Tolman, Oppenheimer and Volkoff 1939) | live verification against ageing: the capacity bound | `Schedule.some_standing_lapses` (Physics.lean) | the limit is attained and has a number, r·W |
| Holography: capacity scales with the boundary ('t Hooft 1993, Susskind 1995; Bekenstein 1981) | the minting pair is the field's root (depth 0, T32) and the instance's boundary (G0); its budget bounds the standings it keeps live, and the interior rearranges without changing it | Physics.lean with `Config.relayout_never_votes` | holographic per Duality, not per instance: every layer brings its own Duality (T38), so depth multiplies the budget |
| Spin networks: area on the links (Rovelli and Smolin 1995); ER=EPR (Maldacena and Susskind 2013) | parts are nodes, standings and admissions are edges, a boundary's area is the count of edges that cross it (the grant graph the record holds, T32) | `Recipe` lines; `Recipe.extend_preserves_decisions` | an edge is bound to grantor, holder and evidence and made by an act of both halves, never by the field |
| Min-cut equals max-flow (Ford and Fulkerson 1956); Ryu and Takayanagi (2006) | inside, a hop is a gate crossing (C1), so fewest hops is fewest crossings; outside, the cut is the floor for every arrangement (T31) | definitional on C1; `Floor.road_gate` (contained items at flow zero) | the owner's two optima coincide inside and are both trivial outside (B4) |
| Prefix codes and the entropy bound (Shannon 1948; Huffman 1952); demand-aware networks (Avin and Schmid 2019) | Axiom 3's layout for root-directed demand is the b-ary Huffman tree of the demand, within one hop of H(D) / log₂ b | `R2Stable.st_settles`, `st_equilibrium_not_optimal` (finding F2) | two witnesses recompute and sign the tree (`ms_accepted_agrees`); the bounds and the convergence are theirs |

The equivalence principle (T23: inside, a trusted part passes every door; `Recipe.decide_pass_iff`) and general covariance
(`Config.relayout_never_votes`) map with no difference at all.

## 2. The cost model (a): Axiom 3's layout at Axiom 1's price

The quantities are DMP's. A Duality's witnesses perform at most r checks per tick (T3a gives each half at least three nodes to perform
them); a standing has validity W ticks (Axiom 2: none longer than the minting accepts); a child holds a standing from both halves, so
keeping it live costs two checks per window; L is the number of acts the Duality serves across its boundary per window (exports,
surfaces, exits: T19, T25, C12); D is the demand over items; a hop is one door (C1), where both halves verify the message by a fixed table
(C2, rules 1 to 16) at a cost that does not depend on how many siblings the node has.

- **Per link.** Two live checks per child per window: 2b + L ≤ r·W, so b ≤ (r·W − L) / 2 (`Schedule.budget_upTo`, each child counted twice).
- **Per hop.** O(1): C2's table takes no sibling as input. A door checks the message, never the fan-out.
- **Hops.** For root-directed demand the expected depth of a b-ary tree is at least H(D) / log₂ b (Shannon's noiseless coding bound) and
  the b-ary Huffman tree reaches it within one hop; for peer demand the floor is the conditional entropy of the demand (Avin and Schmid).
  Both fall as b grows.
- **The optimum.** Every term wants the largest b the budget allows: b* = ⌊(r·W − L) / 2⌋, depth about H(D) / log₂ b*. No interior optimum,
  no constant: not 2, not e, not 3.59. Radix economy's b·log_b N appears only when a hop costs b, which it would if a door verified all b
  children per request; DMP's door does not, so e does not arise in DMP's objects.
- **The two trees.** The 2 the owner predicts is real, on the other tree. A part is a Duality of two halves and a half is a part (the words,
  2026-10-26 23:28Z): the trust tree is binary by definition, valence 3 at every inner node (the part above, the two halves below), grounded
  in G0's constituents. The information tree (the layers of Axiom 3) has the budget fan-out b*. The constants DMP's objects carry are 2
  (the halves, Axiom 1) and 3 (the node floor per half, T3a, a premise); e occurs nowhere.
- **The prediction.** "Branching 2" is a definition on the trust tree, which no benchmark can refute, and falls on the information tree
  under this model. **Refuter of the model:** the benchmark below not giving a straight line, or a measured information tree whose fan-out
  stays at 2 while the budget allows more.
- **Benchmark** (synthetic data, the sandbox pair, no real system; the charter): (1) fix the nodes per half and the window W; (2) add
  synthetic clients one at a time, each holding a standing from both halves, until the first staleness alarm (T4's timer) fires, and record
  the count as the capacity at L = 0; (3) add boundary acts in equal steps of L and repeat (2) at each step; (4) plot clients against L.
  Expected: a line of slope −1/2 from (r·W) / 2 to zero at L = r·W, the counts-only and the extremal cases of Physics.lean. A knee says a
  second budget exists (the record's write rate, Axiom 3, is the first candidate); another slope says the per-act cost is not what C2's
  table prices; a plateau at 2 confirms the owner against the model.

## 3. Theorem candidates (b), each with its Lean and its refuter

- **B1, the capacity bound.** Over a window of W ticks under r checks per tick, standings kept live plus acts served across the boundary
  never exceed r·W; when the declared standings exceed what is left, one is never refreshed in the window, lapses (`lapsed_never_ok`),
  passes nothing (`Gate.stale_never_passes`) and leaves its item contained (T37). Proven: `Schedule.some_standing_lapses`,
  `touched_le_budget`, `extremal_keeps_nothing`. It is the only place where Axiom 1's balance, trust ageing against live verification, is a
  number, and it is the owner's IT instance (02:21Z) verbatim. **Refuter:** a DMP-complete instance that keeps more than r·W standings live
  over a window; the pigeonhole says that needs a standing with no validity, which Axiom 2 forbids.
- **B2, the content-free readout.** Two record entries that agree on time and three verdicts are the same entry (`Entry.ext`): with T31 it is
  DMP's no-hair theorem. **Refuter:** a record field that carries content; the type has none, and a model that adds one breaks T21 and T31.
- **B3, censorship for minted pairs.** A single cause of a declared class never passes an act alone on a minted pair; a pair that is not
  minted is passed by one cause; and no act or loss turns a minted pair into a pressed one, since the loss of a half leaves the gate at hold
  (T3d) and the pair is reminted, never continued (T24b, G0). Proven for the first two (`DoT.confined_influence_never_passes_alone`,
  `DoT.not_minted_collapses`); the third is `Gate.one_witness_never_acts` with the silent half read as hold, no new Lean. **Refuter:** an
  act in DMP that removes one half and leaves the other acting; T24b forbids it, and a text that allowed it would refute this.
- **B4, hops are crossings.** Every hop is a door (C1), so a route's length is its number of gate crossings, and the fewest-hops layout of
  Axiom 3 is the fewest-crossings layout: the owner's min-leakage arrangement and his median are one optimum inside. Definitional, no Lean
  written. **Refuter:** a forwarder that receives a value it is not trusted for; C3 forbids it (it receives the count or the ciphertext), so
  the identity holds for every hop that carries plaintext and bounds exposure from above for the rest.
- **B5, the field is recorded information.** Depth and mass are functions of the lines alone (`Recipe.digest_congr`); freshness is a function
  of the recorded time of the last live verification, which is an act and so an entry (Axiom 3). The owner's sentence of 02:57Z holds for
  grants and verifications; the live freshness is derived from them, not stored beside them. **Refuter:** a freshness read from anything but
  a recorded verification; Axiom 2 forbids an earlier read or a memory.
- **B6, erasure keeps existence.** A destruction is an act, so it leaves exactly one entry, and the item stays destroyed under every later
  tick (`Record.step_records_once`, `Floor.destroyed_stays`). **Refuter:** a destruction that leaves no entry; K3 forbids.

## 4. The definitions challenged (the owner's method rule, 02:33Z)

Each took a clearer, more general form, or held. *Fan-out* split into the trust tree's (2, by the words) and the information tree's (the
budget). *Leakage* split into outside (the floor, the same for every arrangement) and inside (hops, which are crossings). *Entropy* split
into outside (the item's size in bits, T31's random bytes) and inside (zero given the record: one layout per signed state, `ms_one_layout`),
so the ninth sentence is true of every contained item and is the definition of containment, not a condition on some. *Pressure* became the
verification budget, not admission itself. *Boundary* held: the minting draws it (G0) and the pair sits at depth 0 (T32), so root and
boundary are one place, which is why holography reads per Duality. *Placeless* became an outside view. *Black hole* became every minted
instance at the floor and *naked singularity* the pressed instance, as T23 and T-P already say. *THE number to optimise against* (02:50Z)
exists and is attained, not approached: the least a reachable item can expose is one admission to one Duality (two halves, each a cluster
of at least three nodes, T3a); below that is collapse (T37); the Carnot shape is not DMP's, whose bounds are counts and are reached. *Spin*
(the tenth sentence): each exposed field costs budget per read, since every outside read is an act served across the boundary (B1), so an
instance that exposes more keeps fewer clients, monotonically; the counts-only instance is the Schwarzschild case, the budget fully served
the extremal one; the temperature analogy flips (an extremal Kerr hole is cold, a DMP boundary with no clients is maximally stale) and is
not kept.

## 5. Questions for physicists (c)

None that is new. The pass found one place where DMP's objects touch an open question: whether a horizon, once formed, can be uncovered by
a process that lowers its mass, evaporation included (weak cosmic censorship speaks of formation; the end state of Hawking evaporation is
open). DMP's analogue is a theorem (B3) only because DMP destroys the contained item before the cipher's lifetime ends (T31): it chooses
non-unitarity, Hawking's 1976 position, abandoned because information loss costs energy conservation or locality (Banks, Susskind and
Peskin 1984). DMP has no energy, so the objection does not apply and the analogy ends. Asking would be asking the information paradox
again with new words; it is not posed.

## 6. Dropped, one line each

- **Pressure keeps the singularity clothed** (as physics): pressureless dust collapse forms the horizon first (Oppenheimer and Snyder 1939);
  naked cases need fine tuning (Christodoulou 1984, Choptuik 1993). Dropped as physics, kept as DMP in B3.
- **Information equals mass and spans the radius:** capacity scales with area, S = A/4, not with mass; Vopson 2019 is a conjecture. Dropped.
- **The placeless interior:** one signed layout per state (`ms_one_layout`); placeless only from outside. Dropped as a mirror.
- **Planck cells in a volume:** the holographic bound forbids counting by volume; DMP's cell is a Duality and its count grows by extension
  (`Recipe.extend`), an interior quantity; the boundary quantity is the budget (B1). Dropped.
- **Hierarchies pulled toward e:** cost-model dependent and absent from DMP's cost (section 2). Dropped.
- **The ratio 3 and inflation:** nothing in GR or cosmology stops at 3, and DMP has no expansion term: nothing moves a boundary but a
  two-witness act (Axiom 1, the words). Dropped.
- **The wave-particle duality:** complementarity is one aspect or the other, the Duality of Trust both at once; the Englert, Greenberger and
  Yasin inequality needs partial trust, and T23 has none. Dropped.
- **The Page curve:** the radiation never carries content and the record ends by destruction, so the curve is flat at zero and has no Page
  time. Dropped (section 5).
- **Dark matter:** one structural match (collisionless, which is member isolation and the frame rule) and no measured property (the
  five-to-one ratio, the halo profile). **Dark energy:** no DMP quantity scales with the boundary and drives a layer outward. **Force
  carriers:** standings are edges bound to grantor, holder and evidence, made by acts and not by the field. All three dropped as names.
- **The rename of IM:** the owner's naming decision, not a question of this pass.

## 7. The DoT-shaped learner (the owner's AI hypothesis, 4.2; speculative, outside the physics)

In DMP's objects a learning system is DoT-shaped when it is a part: a Duality whose trust half holds standings on live evidence (what the
system may do now, each with a validity that lapses unless re-verified, Axiom 2) and whose information half holds the record and the
layout (what it knows and where, Axiom 3), with every act, an output, a weight update, a tool call, gated by both halves and the stricter
verdict standing (Axiom 1). What the cited pairs lack, exactly: an actor-critic (Barto, Sutton and Anderson 1983) scores an act the actor
still takes; a discriminator (Goodfellow et al. 2014) judges a sample the generator still emits; a verifier beside a generator (AlphaProof
2024; Garcez and Lamb 2020) checks a proof the generator may still offer; dual-process accounts (Kahneman 2011) and predictive coding (Rao
and Ballard 1999; Friston) run two signals in opposite directions with neither gating the other's every act; none records both verdicts
per act. The Lean applies as it stands: `Gate.one_witness_never_acts` says an output one half did not pass is not emitted, for any judges,
once the system's acts go through the gate. What it does not supply is the substance of the shape, independence: two models trained on the
same data by the same author on the same hardware share declared causes and are one witness (T29, `shared_cause_breaks_independence`); a
DoT-shaped learner needs a failure-class list for learners (training data, weights, author, hardware, prompt), minted like any other (T4),
and its halves independent under it. Whether such a system is "more AGI" is not a question DMP's objects can state and is not posed; G0's
clause stands: a part recognized as true AGI is a constituent of G0, so such a learner sits at the ground, never below it. **Refuter:** a
system that emits an output no second half passed and is still called DoT-shaped; then the shape is a name.
