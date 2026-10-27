# DMP applied to quantum gravity: the second witness

The owner's goal for this pass (2026-10-27 06:35Z, verbatim): "Either prove a useful approach to Quantum Gravity through the axiom system,
or prove that the actual intended axiom system, as applied to QG, does not hold and if, exactly where at every context level you can
imagine." This file is an independent second witness. It was written blind to the parallel Fable thread of the same prompt, and read Team
Fable's drafts on `claude/stoic-heisenberg-cs3cpt` (`docs/physics.md`, `docs/qg-attempt.md`) only after the derivation in section 1 was
fixed. Theorem numbers are DMP 0.9.8 (`45d3822`, `main`). Nothing here changes DMP. Every physics result is cited, none re-derived.

## The verdict

**Both halves of the owner's question get an answer, and they are not the same answer.**

1. **DMP does not give a quantum theory of gravity, and cannot.** Applied to physics, the axioms force the trust half to be *classical*:
   two independent witnesses that each read a record in full (Axioms 1 and 3) can only share states that commute, by the no-broadcasting
   theorem. Read "trust is gravitational" (Axiom 2) literally, and the gravitational field cannot be quantized. Every programme that
   quantizes geometry (strings, AdS/CFT, ER=EPR, loop quantum gravity) is therefore excluded by the axioms, not merely missing from them.
2. **DMP does give a useful approach to the quantum-gravity *question*: it picks a side, and that side is testable.** What the axioms
   describe, exactly, is the *classical-gravity, quantum-matter* hypothesis: geometry is a classical, stochastic, local field that records
   mass-energy and nothing else, and matter stays quantum. That is a live, published programme (Oppenheim, PRX 2023; Diósi 1987; Penrose
   1996). It predicts that gravity, acting locally, cannot entangle two masses, and that matter decoherence and spacetime diffusion obey a
   trade-off. Experiments being built now decide it.

So the axiom system holds as a theory of the **classical half** of physics and of how it may couple to a quantum half; it fails as a
theory that **quantizes** gravity, and it fails at one exact sentence: Axiom 3's "every witness of that act can read [the record] in full",
applied to the gravitational field. If gravity is ever shown to entangle masses by local means, that is the sentence that breaks.

## 1. The work: from the three axioms to classical gravity

To apply DMP to physics, its undefined words (the words) need a physical reading. This is the only interpretive step, and everything after
it is a cited theorem:

- a **witness** is a physical system that records (an apparatus, an environment fragment);
- an **act** is an interaction; **evidence** is what a witness's record holds after it;
- a **standing** is a record with a validity; the **trust half** holds standings, the **information half** holds content.

The chain, each step with its source:

| Step | Statement | From |
|---|---|---|
| P1 | Every act on trust is decided by two independent witnesses, each with full reach over it | Axiom 1 |
| P2 | Every grant, use and loss of trust leaves a record that every witness of the act can read **in full** | Axiom 3, sentence 1 |
| P3 | Each witness verifies the standing itself, live, at the point of use, never through a carrier | Axiom 2, sentence 1 |
| T-A | So the state of a standing is reproduced in full on two independent systems: it is **broadcast** | P1, P2, P3 |
| T-B | A set of quantum states can be broadcast if and only if its members commute pairwise | No-broadcasting theorem (Barnum, Caves, Fuchs, Jozsa and Schumacher, PRL 1996) |
| T-C | So the possible states of a standing are jointly diagonal: **trust is a classical variable** | T-A, T-B |
| P4 | "Trust is gravitational. It is a field" | Axiom 2, paragraph 2 |
| **T-D** | **The gravitational field is classical** | T-C, P4 |
| P5 | "No information is ever trusted" and "from trust nothing can be derived about information but its existence" | Axioms 2 and 3 |
| T-E | Content is never broadcast, so it may stay quantum. **Matter (information) is quantum, gravity (trust) is classical** | P5, T-B |
| P6 | Neither half overrules the other; each is gated only by the other | Axiom 1 |
| T-F | So the coupling runs both ways (matter moves geometry, geometry moves matter). Any consistent coupling of a classical system to a quantum one with back-reaction must be **stochastic**: it decoheres the quantum side and makes the classical side diffuse, and the two rates trade off (long coherence demands strong diffusion relative to the coupling) | Oppenheim, PRX 13, 041040 (2023); Oppenheim, Sparaciari, Šoda and Weller-Davies, Nat. Commun. 14, 7910 (2023) |
| T-G | A classical mediator acting by local means is an LOCC channel, and LOCC cannot create entanglement: **gravity does not entangle two masses by local means** (locality is P3's "at the point of use") | Bose et al., PRL 119, 240401 (2017); Marletto and Vedral, PRL 119, 240402 (2017); Horodecki et al., RMP 81, 865 (2009) |

What the chain also says, as checks that it is the right reading:

- **The deterministic version is excluded by DMP itself.** Mean-field semiclassical gravity (Møller 1962, Rosenfeld 1963: curvature set by
  the expectation value of matter) trusts an average nobody verified. Axiom 2 forbids that ("never a claim, a memory"; "without evidence
  for an act, the act does not happen"), and physics rejects it on its own grounds: a deterministic nonlinear coupling signals faster than
  light (Gisin 1990) and is in tension with experiment (Page and Geilker 1981, interpretation-dependent). The axioms select the stochastic
  version, the one that survives.
- **The owner's refresh rate is the reason it is consistent.** The note of 03:26Z ("That's why it was essential that I included the
  refresh rate, otherwise it would have been a scalar field") has an exact counterpart: a classical-quantum coupling without a rate (a
  deterministic one) is inconsistent; with a rate it is consistent, and the rate is the price (T-F). DMP's freshness that decays unless
  re-verified (Axiom 2, T32) is the diffusion term.
- **"From trust only existence" has a number.** Gravity couples universally to energy-momentum and to nothing else (the equivalence
  principle), and energy bounds how much information a region can hold (Bekenstein 1981). So the classical field learns how much is there,
  an upper bound on the count, and never what it says: Axiom 3's sentence, quantitatively.
- **The one "2" that the physics does produce.** Hiding n qubits needs exactly 2n classical key bits, against n for classical bits
  (Ambainis, Mosca, Tapp and de Wolf, FOCS 2000); moving one qubit needs two classical bits plus a shared entangled pair (teleportation,
  Bennett et al. 1993). This is DMP's T39 in quantum form: content moves only with a classical grant, and the grant costs two classical
  bits per qubit. It is a ratio of trust to information, not a fan-out; it does not rescue the branching-2 prediction (section 4), but it
  is the honest place where a 2 appears.
- **The same structure is already in quantum cryptography.** Wiesner's quantum money (1983, "Conjugate coding") is a classical secret
  record held by the issuer plus an unclonable quantum token, verifiable only with both: a Duality of a classical trust half and a quantum
  information half.

## 2. Where it fails, level by level

| Level | Holds or fails | Exactly where | Source |
|---|---|---|---|
| The words (interpretation) | holds, with one reading fixed | witness = recorder, act = interaction, evidence = record (section 1); another reading must say what a witness is physically | this file |
| Quantum information | **holds for the trust half, fails for content** | Axiom 3's "read in full by every witness" is possible only for classical records (T-B); content survives only because Axioms 2 and 3 never broadcast it | Barnum et al. 1996; Zurek, quantum Darwinism, Nat. Phys. 5, 181 (2009) |
| The gate (Axiom 1) | holds as classical | a verdict computed from locally verified evidence is a local hidden-variable model and obeys the CHSH bound; that limits the **verdicts**, not the content they gate | Bell 1964; CHSH 1969; Team Fable `NoGo.lean`, section 4.2 |
| Classical GR | holds as a map, not as a dynamics | horizon = containment, no hair = counts-only readout, area theorem = record only grows; the axioms do not yield the Einstein equations or G (they fix the class of theory, not its law) | Penrose 1965; Israel 1967; Hawking 1971; Jacobson 1995 |
| Semiclassical gravity | **holds: selects the stochastic version** | Axiom 2 excludes mean-field (Møller–Rosenfeld); Axiom 1's two-way gating forces back-reaction; T-F forces stochasticity | Oppenheim 2023; Gisin 1990 |
| Black holes | holds for containment, fails for entropy | DMP's evaporation destroys content before the cipher dies (T31), the non-unitary answer, which is the classical-gravity programme's answer too; but DMP's capacity is extensive (it grows with the number of Dualities, every layer bringing its own, T38) where Bekenstein–Hawking is an area law, so DMP's interior is **not holographic** | Hawking 1976; Bekenstein 1981; 't Hooft 1993 |
| Quantized-geometry programmes | **fails, by the axioms** | ER=EPR makes connectivity (trust) out of entanglement (information): Axiom 2's "no information is ever trusted" forbids exactly that. Loop quantum gravity and strings put geometry in superposition: T-D forbids it | Maldacena and Susskind 2013; Van Raamsdonk 2010; Rovelli and Smolin 1995 |
| DMP's own field, T32 | **fails as gravity** | the VIBE field is a sum of isolated per-member terms over a graph of pairwise grants; a gravitational field couples every place to every other. Pairwise classical channels as a model of gravity are already ruled out by atom interferometry | Team Fable `NoGo.lean` 4.1; Kafri, Taylor and Milburn 2014; Altamirano, Corona-Ugalde, Mann and Zych, arXiv 1612.07735 (CQG 2018) |
| Experiment | **open: this is the test** | (1) gravity-induced entanglement observed, with nonlocal classical explanations closed off, refutes T-G and with it P2-on-gravity; (2) the decoherence-diffusion window closed from both sides refutes T-F; (3) the parameter-free Diósi–Penrose collapse is already ruled out, the parametrized classical-gravity models are not | Bose et al. 2017; Oppenheim et al. 2023; Donadi et al., Nat. Phys. 17, 74 (2021) |
| Cosmology | no DMP number | stochastic classical gravity has been proposed to mimic dark matter in rotation curves, and that claim is disputed; DMP adds no quantity to it | Oppenheim and Russo, arXiv 2402.19459; Hertzberg and Loeb, arXiv 2404.13037 |
| DMP engineering | unaffected | every theorem about CMOS stands whichever way the experiments go | gravity `evidence/` |

The one open theoretical point that touches T-G directly: whether classical gravity can produce entanglement by *local* means is disputed
right now (Aziz and Howl, Nature 2025, say yes when matter is a quantum field; several comments, e.g. arXiv 2511.07348 and Gundhi,
Infantino and Bassi, arXiv 2604.19696, say no). If Aziz and Howl stand, a positive entanglement experiment no longer refutes classical
gravity, and T-G loses its sharpness; T-A to T-D do not depend on it.

## 3. The sharp questions, for physicists and for the owner

1. **For a physicist (yes or no):** is "the gravitational field is the one record every subsystem can read in full", a broadcastability
   postulate that forces classicality by the no-broadcasting theorem, already a stated motivation for classical gravity in the
   classical-quantum literature? If yes, DMP arrived at a known position by a new road and should cite it as such. If no, that one
   sentence is the contribution worth a physicist's time.
2. **For the owner (a choice the axioms force):** to keep "trust is gravitational" as physics, accept that DMP predicts gravity is **not**
   quantized, and stake the physics section of the paper on the entanglement and decoherence-diffusion experiments. To aim for a quantum
   gravity instead, Axiom 3's "read in full by every witness" must be dropped for the gravitational field, and then DMP no longer says
   anything about gravity that the physics does not already say.

## 4. The hypothesis list, one line each

| Item (c-constraints section 4.1, 4.2) | Verdict | Why |
|---|---|---|
| Information pressure keeps the singularity clothed | dropped as physics | pressureless collapse forms the horizon first (Oppenheimer and Snyder 1939); kept only as DMP's pressed instance = naked singularity (T-P) |
| Information = mass spans the radius | dropped | capacity scales with area, S = A/4, not with M; Vopson 2019 is a conjecture |
| Cosmic censorship | merged | a minted pair is never exposed by one cause; that is DMP's theorem, not new physics |
| Densest layout, placeless inside, fast scrambling | merged into the black-hole row | DMP's interior is placed (one signed layout) and extensive, so neither Bekenstein-saturating nor scrambling |
| Planck cells in a volume | dropped | the holographic bound forbids counting by volume |
| Links occupy space (spin networks) | dropped for QG | a quantum spin network puts geometry in superposition, which T-D forbids |
| Radix economy, e, and branching 2 | dropped | no DMP cost carries a per-hop cost growing with fan-out, so no interior optimum; the only physics 2 is trust bits per qubit (section 1) |
| Trust-versus-information equilibrium | **kept, transformed** | it is the decoherence-diffusion trade-off of T-F, and that one has an experiment |
| Ratio 3 and inflation | dropped | nothing in GR or cosmology stops at 3; the dark-energy to matter ratio is about 2.2 and changes with time |
| Wave–particle duality | merged | the DoT is not complementarity; it is the classical/quantum split of information (section 1) |
| Min-leakage as min-cut, Ryu–Takayanagi | dropped for QG | Ryu–Takayanagi measures entanglement across a quantum geometry, which DMP's classical trust half cannot carry; kept only as an engineering bound (max-flow, min-cut) |
| Spinning holes leak one more | merged | into the capacity budget; no QG content |
| Capacity budget and its benchmark | kept for DMP, not QG | the classical shadow of T-F; useful engineering, no new physics |
| THE number to optimise against | **kept, transformed** | in QG terms it is the trade-off curve of T-F: the least decoherence a given spacetime precision costs |
| Dark matter 1:1, dark energy surface, force carriers | dropped | no DMP quantity; the dark-matter route exists only through Oppenheim and Russo, and is disputed |
| Possibility space between vectors, refresh rate (03:26Z) | **kept** | it is T-F's rate; without it the coupling is inconsistent |
| Two axioms (03:46Z, "self-propagating" correction) | dropped for QG | without a broadcast trust record the chain loses T-A, so it predicts nothing; it becomes Wheeler's "it from bit" (1990) |
| DoT-shaped learner (4.2) | out of scope | not a physics question |

## 5. The second witness on Team Fable's drafts

Read after section 1 was fixed. Agreement and disagreement, so the owner can weigh two witnesses rather than one:

- **Agree:** `qg-attempt.md` 4.1 (DMP's field is uncoupled, a gravitational field is coupled; also the pairwise-channel refutation above)
  and 4.3 (no field equations follow). `physics.md` section 1 (the map holds as a map) and the dropped list largely match section 4 above.
- **Disagree on scope, `qg-attempt.md` 4.2:** "the gate obeys CHSH, so the theory cannot be quantum" is true of the **verdicts** and does
  not reach the **content**. DMP never makes content evidence (Axiom 2) and never derives content from trust (Axiom 3), so the information
  half is free to be quantum. The correct conclusion is "trust is classical, information may be quantum": the classical-quantum
  hybrid, a live programme, not "no physics". Team Fable's verdict "False" is right for *quantum gravity* and too strong for *gravity*.
- **Disagree, `physics.md` holography row:** "holographic per Duality" is a per-node capacity limit; summed over layers the capacity is
  extensive, so the interior is not holographic. The black-hole row in section 2 says so.

## Lean

None written. T-A to T-G are statements about Hilbert spaces and channels; the evidence chain is core Lean with no Hilbert-space library,
and the derivation adds nothing a kernel check of DMP's objects could decide. What would be Lean-checkable is the interpretive step P1 to
T-A in DMP's own objects (a standing read in full by both witnesses is the same value on both); it is not done here.
