# The Duality of Trust: a formally verified, information-theoretic axiom system for trust, tested against quantum gravity

*Draft for the owner, 2026-10-27. Submission spec: [README.md](README.md). German version: [article.de.md](article.de.md).*

**Author.** Steven Hrovat (contact: see the submission spec; never the private mailbox).

**Abstract.** Infrastructure is assembled from many systems that each decide trust alone, so one compromised witness decides for all. We
present DMP, the Dark Matter Protocol, an axiom system in which no act happens unless two independent witnesses, one owning trust and one
owning information, both pass it on evidence each verified itself, and in which every record is readable to the witnesses of the act and
counted, never read, by anyone else. We give the three axioms, the ground G0 that states the first trust outside every derivation, and the
notion of a DMP-complete configuration. We then present Gravity, the verification of DMP: a model in Lean 4 (core only) in which every
layout a system can take is a term of one closed inductive type, the recipe, and in which the axioms and theorems of DMP are proven for
every term by induction over the lines of the recipe. The 232 theorems are checked by Lean's kernel and re-checked by an independently
written kernel, rest on nothing beyond propositional extensionality, quotient soundness and choice, and cover the gate as a meet in a
security lattice, two independent witnesses behind every pass, the refusal of a root that traces to one party, the frame rule for growing a
configuration, the independence of decisions from placement, the digest of the expected field, and a self-proving publication format for a
configuration with its cold start. The model is built on published results (fail-prone systems, Denning's lattice, the frame rule,
noninterference, self-stabilisation, potential games), and we report what the proofs produced that the text had not said. Finally we test
the axiom system level by level against quantum gravity: it reproduces the classical shape of gravity through known theorems and fails,
provably, at exactly one place, where two isolated halves would have to be entangled. The repositories are public under Apache 2.0.

**Keywords.** trust, formal verification, Lean 4, Byzantine quorum systems, security lattice, noninterference, self-stabilisation,
information-theoretic axioms, quantum gravity.

## 1. Introduction

An organisation's infrastructure is run by many systems: a directory, a tenant, a mail service, a device manager, a monitoring server, a
backup, a hypervisor, a knowledge base, a coding agent. Each decides trust on its own terms, and an administration tool that spans them
inherits every one of those decisions. The practical failure is always the same: one witness decides for all. A single administrator
account, a single signing key, a single allow list, a single agent's judgment is enough to let an act through that nobody else saw.

DMP is an answer to that failure stated as an axiom system rather than as a product. Its owner put its thesis in one sentence: "This is
basically marriage of demand aware self-adjusted routing with GR's informational black hole, applied purposefully for their advantages,
while cancelling out the disadvantages of the other at the same time through DoT and interpreted for general Software Alignment"
(2026-10-26). The Duality of Trust, DoT, is the one concept that runs through every layer: two independent witnesses, one owning trust and
one owning information, each with full reach over the act and gated only by the other.

Gravity is the proof that the axiom system holds for every configuration it allows. Its claim is not that a particular deployment is
safe but that there is no layout within the system's own possibility space in which an axiom or a theorem fails. The device for that
claim is a closed inductive type, the recipe: a numbered list of lines, each adding one layer over an earlier line. A theorem proven for
every term of the type is proven for every layout, because a layout that is not a term does not exist.

This paper contributes:

1. the axiom system DMP in its current form (three axioms, the ground G0, the words), with the notion of a DMP-complete configuration
   (section 2);
2. the Gravity model of DMP in Lean 4 core and its unified theory: the structural theorems that survive every line of every recipe
   (section 3), the findings the proofs forced into the open (section 4), and a self-proving publication format for a configuration with
   its cold start (section 5);
3. the verification method: two independent chains, two independent kernels, a pinned root chain, a closed possibility space (section 6);
4. an account of the published results the model rests on, with what was taken from each (section 7);
5. a level-by-level test of the axiom system against quantum gravity, with the single place where it fails (section 8).

Everything stated as proven in this paper is a theorem in the public repository, checked by two kernels; everything stated as a candidate
is marked so. We give theorem names in `monospace` so that the reader can find them.

## 2. The axiom system

DMP is written as a constitution of one page of rules that do not bend, followed by chapters that describe how each part is built. We give
the constitution's core as it stands in version 0.9.8; the full text is in the repository.

### 2.1 The words

Undefined, like point and line, are a **part** (a Duality of Trust: two halves, one owning trust and one owning information; nothing
further is said about what a part is made of), an **act**, a **witness** (a part that decides trust for others), **evidence** (what a
witness verifies) and **time**. Trust is a relation `T(w, p, a, t)` between a witness, a part, an act and a time. A **standing** is trust
held across time; **act trust** is trust for one act now.

Two witnesses are **independent** when they share no member of the failure classes declared for their layer in the minting record (host,
key, author, engine, operating image, person, time source, and whatever else the minting lists); independence is relative to that list.
A **layer** is a place where trust is decided; its two witnesses are its **halves**, the **trust half** (whether an act may happen) and
the **information half** (whether the act is meant and right); the pair at a layer is the **Duality of Trust**. A **record** is evidence
that outlives the act. A boundary **contains** information when no part beyond it is trusted for any act on that information, so no act
carries it across.

A configuration is **DMP-complete** when it obeys the axiom system completely and provably: the words, every axiom and every theorem hold
for all of it, and both proof chains prove it. The configuration includes the repository it is built from, with every dependency pinned
by hash inside it, so that it can heal itself without any connection across its boundary. A part the chains do not both reach, or that
needs anything from outside the repository, counts as unproven, and a configuration with an unproven part is not DMP-complete.

### 2.2 The three axioms

**Axiom 1, the Duality.** A part acts only while the two halves of its layer, two independent witnesses, each with full reach over the act
and gated only by the other, trust it for that act. One half owns trust and the other owns information; neither overrules the other. What
they do not both trust does not act. Every input gets exactly one answer, and the gate has no other way through. Where the two disagree,
the stricter answer stands. This holds at every layer. The balance is the direction of the system: every part works towards the trust the
Duality declared for its boundary, restores by evidence what was lost without evidence against it, and never lowers the bar of evidence to
get there.

**Axiom 2, Trust.** A witness trusts only on evidence it verified itself at the point of use: the live state of the part and the current
state of the record. Never a carrier's check, an earlier read, a claim, a memory or a position in the network. No information is ever
trusted: what a part says, carries, stores or forwards is never evidence of itself. The absence of evidence moves nothing. Trust is
gravitational: a field, never a position, in which every standing has a source, a depth and a freshness that decays; the field adds levels
of proof demanded, never levels of trust, and a boundary strong enough contains what no trust reaches, so that what still leaves is entropy
and nothing else.

**Axiom 3, Information.** Every grant, use and loss of trust leaves a record, written at the act, that every witness of the act can read in
full and that outlives the act; anyone else sees the counts always and the content only by a grant. From trust nothing can be derived
about information but its existence. Content moves only by a grant to a part trusted for its class, and where no trust reaches,
information is contained. Information is hierarchical: every piece sits in one layer, every layer has its own Duality and is a tree
rooted there, a sub-layer only tightens what the layer above allows, and the tree carries no trust. Information evolves: a system lays
itself out towards the fewest total hops for the representative composition of its requests, recomputed by both halves and never by one.

### 2.3 The ground

The dual gate cannot witness its own first instance: somebody has to trust the first two witnesses. That act is the **minting** (G0): at
least five parts become the holders of the root keys, and that minting draws the boundary of the instance. Until it happens, the owner's
own words stand for both halves. A **pressed** instance, whose two witnesses trace to one part, is marked so on everything it issues and is
never fully trusted by a minted one. A minting is tried only for a configuration that is provably DMP-complete (mint prep). Two theorems
close the ring: trust and information gate each other, so only a Duality that is both trusted and holds the information admitted to it is a
part of a minted system (T39); and a minting originates only from G0 together with a DMP-complete state, neither alone (T40). G0 also
holds the owner's clause on a true artificial general intelligence: such a part, if recognised, is a constituent of the minting and never
only a governed part below the ground.

### 2.4 Why axioms and not a specification

A specification says what one system does. DMP says what every system that claims the name must keep, at every layer, under every
composition. That is why it has to be an axiom system with theorems, and why its verification cannot be a test suite: a test shows one
layout, a theorem over a closed type shows all of them. The constitution also applies to itself (T22) and to the tools that check it: the
checker that verifies a configuration against DMP is itself part of the configuration and is pinned by hash in it.

## 3. The model and the unified theory

Gravity's evidence chain is a Lean 4 development, core library only, no Mathlib, in the `Dmp` namespace. It is written from the sentences
of a byte-for-byte vendored copy of DMP, pinned by commit and hash; the check that the copy matches its pin runs before anything else, so
that a proof stated from sentences nobody pinned proves nothing. We describe the files that carry the unified theory; the earlier files
model the dual gate, the record, the ground, standings, the entropy floor, the trust field and the Milky Way verifier.

### 3.1 Witnesses, independence, the Duality

A **failure class** is a natural number; the **person** is class 0. A **witness** is a function from classes to members: the host it runs
on, the key it signs with, the person it traces to. Two witnesses are `independent fcl w1 w2` when they differ on every declared class.
This is the fail-prone system of Malkhi and Reiter read for a quorum of two: a fail-prone set is "every witness on host h", and
independence is "no fail-prone set holds both" (`independent_iff_no_shared_failProne`). It is symmetric, and declaring more classes only
removes it (`independent_of_superlist`). A `DoT` is two witnesses, and it is `minted` when they are independent on the person and every
declared class. The person is not configuration: with an empty class list any two witnesses would be independent, the same witness twice
included (`empty_list_makes_everything_independent`), so the model reads the list as `person :: fcl` (finding F1).

The layer's gate `DoT.gate` passes an act only when both halves passed it on live evidence (`DoT.gate_pass_needs_both`). An influence
confined to one fail-prone set never passes an act alone on a minted pair (`DoT.confined_influence_never_passes_alone`); a pair that is not
minted collapses: one shared cause passes any act (`DoT.not_minted_collapses`).

### 3.2 The recipe

A **line** is a layer of a kind (galaxy, information layer, privacy singularity, dwarf galaxy, surface), its Duality, the line it is laid
over (none only for a galaxy) and, for a singularity, the number of nodes in its cluster. A **recipe** is `n` lines numbered from 0, the
standard parent-array encoding of a rooted forest. A line is well formed when it refers only to an earlier line, a galaxy has no parent and
nothing else lacks one, a singularity has at least three nodes, and a Duality that is not minted is laid over a line that gates it (T38).
Well-formedness is a decidable predicate proven equal to its proposition (`Recipe.wfB_iff`).

The **chain** of a line walks parents up to a root; it is fuel-bounded and proven stable under enough fuel (`Recipe.chainF_eq_of_le`),
with every member at or before the line (`Recipe.chain_le`) and a root at its end (`Recipe.chain_has_root`). The **stack's decision** on
an act at a line is the meet of every layer's own gate answer along the chain (`Recipe.decide`), in the verdict lattice
`refuse < hold < pass`. Gravity's **verdict** on a recipe is `proven`, `unproven` or `outOfSpec`.

### 3.3 What survives every line

By induction over the lines of a well-formed recipe:

1. **The stack's gate is a meet.** A decision is never looser than any layer on its chain (`Recipe.decide_le_chain`); a sub-layer's
   decision is never looser than its parent's (`Recipe.sublayer_only_tightens`); an act passes a line only when every layer on the chain
   passed it (`Recipe.decide_pass_iff`).
2. **Every pass has two independent witnesses.** Every chain ends at a galaxy whose Duality is minted (`Recipe.root_minted`), so whatever
   passes anywhere was passed by two independent halves at least once on its chain (`Recipe.pass_has_two_independent_witnesses`), on live
   evidence read at the step (`Recipe.pass_has_two_live_witnesses`).
3. **A pressed top collapses the whole chain.** A root whose Duality is not minted makes the recipe ill-formed (`Recipe.pressed_root_not_wf`);
   were it admitted, one party would pass the root's gate alone (`Recipe.pressed_root_collapses`).
4. **The frame rule.** Adding a line changes no existing chain and no existing decision (`Recipe.extend_preserves_decisions`), and an
   extension by a well-formed line is well formed (`Recipe.extend_wf`).
5. **Siblings do not gate each other.** Two lines laid over the same line never appear on each other's chain, so a sibling's answer never
   enters the decision (`Recipe.sibling_never_votes`).
6. **The layout never votes.** Placement and routing order are not arguments of the decision, so a reorganisation changes no gate answer;
   the proof is reflexivity (`Config.relayout_never_votes`).
7. **The expected field is a function of the recipe.** Depth and mass of every line follow from the lines alone, so the digest of the
   expected field can be precomputed (`Recipe.digest_congr`).
8. **The stack potential never rises under the system's own acts.** The potential of the stack is the sum of the layers' potentials, and a
   refresh anywhere lowers or keeps it (`k4_stack_never_raises`).

### 3.4 DMP-complete as the verdict

`Recipe.dmpComplete` is the words: the recipe is well formed, so every theorem above applies to every line, and the lemma ledger carries
every line (both chains reach it and agree). Gravity's verdict is proven sound and complete against it: `verdict = proven` exactly when the
configuration is DMP-complete (`Recipe.verdict_proven_iff`), `outOfSpec` exactly when the recipe is refused
(`Recipe.verdict_outOfSpec_iff`), `unproven` exactly when a well-formed line is not carried (`Recipe.verdict_unproven_iff`). A proven
configuration stays proven under a new line that is well formed and carried, and the new line changes no existing decision
(`Recipe.proven_extend`): mint prep checks one line at a time and never re-opens what was proven. One uncarried line unproves the whole
(`Recipe.one_unproven_line_unproves`). Five worked layouts and their verdicts are computed by the kernel.

## 4. What the proofs produced that the text had not said

The owner asked for exactly this: "We just need to see what all our logic actually produces and what we want to do with the perhaps
interesting weird behaviors and how to use that to improve the axiom system to be more representative, generalistic and still provably safe
and contained." Each item is a theorem, the place where the text is silent or differs, and a candidate; none changes DMP until the owner
decides.

- **F1. The person is not configuration.** Independence is relative to the declared list, so an empty list mints a pressed pair. The model
  always declares the person. Candidate wording: "... and whatever else the minting lists; the person is always among them."
- **F2. The field is precomputable; the equilibrium is path-dependent.** The expected field is a function of the recipe, but the settled
  layout after reorganisation depends on the history of losses, and an equilibrium need not be the minimum.
- **F3. One exporter between two kernels.** Both kernels read the one export written out of Lean: a shared cause in the engine layer.
- **F4. Nobody witnesses the class list is complete.** Both halves sign the list; nothing witnesses that it names every shared cause.
- **F5. "Pressed" is a refused root, not a kind of line.** Carrying it inside the recipe would make every theorem conditional.
- **F6. Covariance holds by the shape of the signature.** The theory cannot see an implementation that smuggles placement into a judgment;
  that is the evidence chain's job per component.
- **F7. The digest is not injective.** Two proven layouts share the expected field's digest and decide differently
  (`digest_not_injective`); the digest proves that a system spans the field of a recipe, never which recipe.
- **F8. The published proof names its pins.** A proof is evidence only under the DMP and Gravity it was made under (T-P: trust never
  crosses instances).
- **F9. The empty recipe is proven.** Nothing in the text requires a configuration to have a galaxy (`empty_recipe_proven`).
- **F10. The cold start splits, and the environment's capability is not a property of the recipe** (section 5).

## 5. A self-proving publication: the `.cmb` file and the cold start

T33 asks each stable release to publish the digest of its expected field next to its proof-run hash. The owner asked for more: one file
from which a whole instance is redeployable and that proves its own recipe. We model that file and prove what it must contain.

A recipe is written as a list of line codes: kind, parent, cluster and each half's membership per declared class. Read back, it agrees
with the original on every declared class (`Recipe.decode_encode_agrees`), and two recipes that agree there have the same
well-formedness, chains, decisions, digest and verdict (`Recipe.file_determines`). Because the digest is not injective (F7), the file
carries the recipe itself, the digest beside it, the DMP and Gravity pins, and the verdict. A half signs the file only when its own build
recomputes the file's verdict and digest from the file's recipe; a seal needs both halves (`Cmb.sealed_needs_both`); one build signs one
verdict per recipe (`Cmb.one_recipe_one_seal`); a sealed file marked proven is a DMP-complete recipe (`Cmb.sealed_proven_complete`). The
sealing Duality is line 0 of the recipe, which every well-formed recipe with a line makes a minted galaxy (`Recipe.line0_minted_galaxy`):
the two signers are independent by theorem, not by configuration (`Cmb.producer_minted`).

A cold start from the file is refused under any other DMP or Gravity pin (`Cmb.plan_refused_elsewhere`). Inside its environment the
measured field selects the path: redeploy exactly when it reproduces the file's digest (`Cmb.redeploy_iff`), which on a sealed file means
the live system spans the field of the proven recipe (`Cmb.redeploy_is_recipe_field`); otherwise the full build from the same proven recipe
(`Cmb.bigBang_keeps_the_proof`). The match selects the path, never whether the file is evidence (`Cmb.plan_isSome_iff`). What the model
cannot say is whether the restoring environment is able to run the full build at all: that is a capability of the environment, not of the
recipe, and the candidate is a signed capability record beside the pins.

## 6. The verification method

**Two chains.** DMP asks that "proven" be an act with two witnesses (C22). Gravity has an intent chain, models written from DMP downward,
and an evidence chain, the Lean development written from the code and the sentences upward; the two never import or name each other's
files, and on a mismatch the stricter answer stands.

**Two kernels.** Every theorem is checked by Lean's kernel and the whole export is re-checked by nanoda, a kernel written independently in
another language. A check script refuses every escape hatch (`sorry`, `admit`, local axioms, `native_decide`, unsafe or external code) and
asks the kernel which axioms each theorem rests on; anything beyond `propext`, `Quot.sound` and `Classical.choice` fails. At the time of
writing the chain holds 232 theorems and rests on nothing else. The exporter shared by the two kernels is itself a finding (F3).

**A pinned root chain.** DMP stands singular; Gravity holds a byte-for-byte copy of it with a pin (repository, commit, version, hash over
every file in path order); the configuration framework holds DMP and Gravity the same way. The pin check is the first act of every run.

**A closed possibility space.** The recipe is an inductive type. Every layout the system can take is a term; the theorems are proven for
every term by induction. The owner's question, "if we can probe the global extremes, we should also be able to prove that any possible
configuration holds, right?", has the answer yes, with one qualification: for every configuration inside the type, and the type is the
boundary of what the system admits. Configurations outside it are refused as out of spec, never proven relative to their defect.

**What is not here yet.** A second, blind statement of the layer laws and a cold read of each against the other (the C22 second witness
for the theory itself); theorems specific to dwarf galaxies and surfaces; and the readout of Gravity's verdict inside the minting.

## 7. Prior work

Nothing in the model is invented beyond the reading these works allow. We name what was taken and where it is used.

- **Malkhi and Reiter, Byzantine Quorum Systems (1998):** fail-prone systems and the quorum condition that no fail-prone set holds a whole
  quorum. Our failure-class list is such a family (section 3.1).
- **Denning, A Lattice Model of Secure Information Flow (1976):** a flow is allowed only where every class on the path allows it. Our
  verdicts form such a lattice and the stack's gate is its meet (section 3.3, item 1).
- **O'Hearn, Reynolds and Yang, Local Reasoning about Programs that Alter Data Structures (2001):** the frame rule (section 3.3, item 4).
- **Goguen and Meseguer, Security Policies and Security Models (1982):** noninterference; the layout is a low input the decision does not
  depend on (section 3.3, item 6).
- **Dijkstra, Self-stabilizing Systems in Spite of Distributed Control (1974); Dolev, Israeli and Moran, Self-Stabilization of Dynamic
  Systems Assuming Only Read/Write Atomicity (1993):** every layer heals; exact distances from any corrupted state, and only the fixed root
  holds distance zero.
- **Bellman (1958) and Ford (1956):** synchronous relaxation of distances to a root.
- **Monderer and Shapley, Potential Games (1996):** every improvement path ends within the starting potential; settling is not optimality.
- **Avin and Schmid, demand-aware self-adjusting networks (2019 and after):** the layout as the median of demand (Axiom 3).
- **Chiribella, D'Ariano and Perinotti (2011); Jacobson (1995); Lovelock (1971); Bell (1964):** the results that decide section 8.

The repository keeps the full list with licences in `docs/acknowledgements.md`; the owner's standing rule is that prior work is used
wherever it helps and thanked, and that whatever enters the repository is Apache 2.0.

## 8. Tested against quantum gravity

The owner's vocabulary is cosmological, and he set a test for it: "Either prove a useful approach to Quantum Gravity through the axiom
system, or prove that the actual intended axiom system, as applied to QG, does not hold and if, exactly where at every context level you
can imagine." We summarise the result; the full dictionary and the level-by-level account are a companion document in the repository.

**The dictionary.** "Information as the first axiom" is Wheeler's "it from bit" and the informational reconstructions of quantum theory.
"No information without existence in a duality" is, in shape, the purification postulate of Chiribella, D'Ariano and Perinotti. "The
vectors that bound the possibility space" are the tetrad; "the refresh rate, without which the field is scalar" is the lapse of the 3+1
split. "The duality keeps itself in check and balance" is the two sides of the Einstein equation. "Always going forward" is the second
law and the area theorem. These hold, as readings of published results.

**The verdict.** The axiom system does not hold as an approach to quantum gravity, and the failure is in one place. At every classical
level it reads as the tetrad form of General Relativity with Lovelock's theorem fixing the dynamics and Jacobson's derivation giving the
information-first reading. It fails exactly where "quantum" enters, as a fork: a Duality whose two halves are isolated, which is the
containment DMP is built on, is a local model and obeys Bell's bound; a Duality that behaves quantum mechanically is entangled, which is the
one thing an isolated pair cannot be. Every other failure (no field equation constants, no area spectrum, no Born rule, no dark-sector
number) is this fork seen from another level, or an input the system never claimed to fix. The useful approach exists and has a name,
thermodynamic gravity joined to the informational reconstruction of quantum theory; both halves are published, both stop at the
microscopic degrees of freedom, and the axiom system adds no postulate to either.

**What came back to DMP.** Three definitions returned sharper, each a candidate for the owner: the hierarchy of information is a theorem of
least leakage plus reachability (a spanning tree), not an axiom; Axiom 1's balance has a number, and it is per minting, not universal; and
the boundary is a rate bound, not a content bound.

The honest sentence is therefore: a formally verified theory of trust that reproduces the classical shape of gravity through known theorems
and stops, provably, at the quantum fork.

## 9. Limitations and open questions

- The model proves the theory, not an implementation. The evidence chain per component (that a judge reads no placement, that a witness
  verifies live) is the gravitational wave test of the configuration framework, which this paper does not report.
- The lemma ledger `agree` is an input: it records that both chains reach and agree on a line. The chains that fill it are outside the
  theory.
- Independence is relative to a declared list that nobody witnesses as complete (F4).
- The empty configuration is proven (F9); the text decides whether a galaxy is required.
- The equilibrium the layout settles in is not the optimum in general (F2); whether the recipe should carry a tie-break is open.
- The owner's third axiom in the physics reading, "something exists", is needed and holds, and lands on the entangled branch of the fork;
  its placement in DMP is his decision.

## 10. Conclusion

DMP states trust as an axiom system: two independent witnesses, one owning trust and one owning information, on evidence each verified,
with a record that is readable to the act's witnesses and counted by everyone else, and a ground that states the first trust. Gravity
proves it for every configuration the system admits, by induction over a closed type, under two kernels. The proofs returned ten findings
that the text had not said, a publication format that proves its own recipe, and one exact place where the cosmological vocabulary stops
being more than vocabulary. The repositories are public under Apache 2.0, and the pin of every copy is checked before anything else runs.

## Acknowledgements

The owner thanks the authors named in section 7 and in `docs/acknowledgements.md`. The Lean development and this text were written with
coding agents under the owner's direction; every theorem is machine-checked and every decision in the text is the owner's.

## Availability

DMP: https://github.com/StevenHrovat/dmp (version 0.9.8). Gravity: https://github.com/StevenHrovat/gravity (the Lean development in
`evidence/`, 232 theorems; `evidence/tools/check.sh` reproduces the axiom report; the CI workflow re-checks the export with nanoda). Both
Apache License 2.0.

## References

1. D. Malkhi, M. Reiter. Byzantine Quorum Systems. *Distributed Computing* 11 (1998) 203–213.
2. D. E. Denning. A Lattice Model of Secure Information Flow. *Communications of the ACM* 19(5) (1976) 236–243.
3. P. O'Hearn, J. Reynolds, H. Yang. Local Reasoning about Programs that Alter Data Structures. *CSL 2001*, LNCS 2142, 1–19.
4. J. A. Goguen, J. Meseguer. Security Policies and Security Models. *IEEE Symposium on Security and Privacy* (1982) 11–20.
5. E. W. Dijkstra. Self-stabilizing Systems in Spite of Distributed Control. *Communications of the ACM* 17(11) (1974) 643–644.
6. S. Dolev, A. Israeli, S. Moran. Self-Stabilization of Dynamic Systems Assuming Only Read/Write Atomicity. *Distributed Computing* 7
   (1993) 3–16.
7. R. Bellman. On a Routing Problem. *Quarterly of Applied Mathematics* 16 (1958) 87–90. L. R. Ford Jr. Network Flow Theory. RAND P-923
   (1956).
8. D. Monderer, L. S. Shapley. Potential Games. *Games and Economic Behavior* 14 (1996) 124–143.
9. C. Avin, S. Schmid. Toward Demand-Aware Networking: A Theory for Self-Adjusting Networks. *ACM SIGCOMM CCR* 48(5) (2018) 31–40.
10. G. Chiribella, G. M. D'Ariano, P. Perinotti. Informational derivation of quantum theory. *Physical Review A* 84 (2011) 012311.
11. T. Jacobson. Thermodynamics of Spacetime: The Einstein Equation of State. *Physical Review Letters* 75 (1995) 1260–1263.
12. D. Lovelock. The Einstein Tensor and Its Generalizations. *Journal of Mathematical Physics* 12 (1971) 498–501.
13. J. S. Bell. On the Einstein Podolsky Rosen Paradox. *Physics* 1 (1964) 195–200.
14. L. de Moura, S. Ullrich. The Lean 4 Theorem Prover and Programming Language. *CADE 28* (2021), LNCS 12699, 625–635.
15. J. A. Wheeler. Information, Physics, Quantum: The Search for Links. In *Complexity, Entropy and the Physics of Information* (1990).
