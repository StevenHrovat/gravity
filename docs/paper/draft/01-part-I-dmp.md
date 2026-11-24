# Part I. DMP: a language for existence

*Draft 4, 2026-11-24. Part I is vocabulary, not mathematics. Every statement in it is a definition of DMP, a reading of DMP, or a
pointer to the precise statement in Part II. Claim labels (I.n) are listed in `../CLAIMS.md`.*

## I.0 How to read this part

DMP, the Dark Matter Protocol, is a specification for systems that must trust each other. It was written for software and
governance: who may act, on what evidence, and what is left behind. Its author reads the same rules as a description of how anything
comes to exist. This paper uses DMP in exactly that way: as a language. It gives names to the steps that the first three problems,
Parts IV to VI, have in common, so that each step is said once.

Two rules keep this honest.

* **A reading is not a theorem.** Where this part says "existence is a positive weight", that is a reading: a choice of which
  mathematical object a DMP word stands for. Readings are marked **[reading]**. They guide; they prove nothing.
* **Every reading points forward.** Each section ends with the precise statement that Part II makes of it, with its status there.
  Part I can be skipped by a reader who wants only the mathematics. It cannot be used by a reader who wants a proof.

The marks used in the whole paper:

| Mark | Meaning |
|---|---|
| **[Lean]** | Machine-checked in this project (Lean 4 with Mathlib, standard axioms only). The module path is given relative to `docs/mass-gap/formal/ProofPhase/`. |
| **[classical]** | Known mathematics or physics, with a reference. |
| **[external]** | A published or posted result by others that this project reads but did not rebuild or re-check. |
| **[conditional]** | Holds under a named assumption (the one assumption of Part III, unless another is named). |
| **[certified]** | Enclosed in ball arithmetic, with its log. |
| **[paper]** | Argued in this project in prose, not machine-checked. |
| **[numerical]** | Measured in this project. Evidence; it can refute, never prove a statement about all cases. |
| **[reading]** | A DMP reading: an interpretation, never mathematics. |
| **[open]** | Not settled by anyone. |

Qualifiers after a comma or semicolon ("from X", "recalled", "traced", "unverified", "an estimate", "re-checked") and the marks
**[sketch]** and **[unchecked]** are defined in the introduction, "How to read the status marks".

---

## I.1 Existence has two halves

**DMP.** The smallest unit of DMP is a *part*, and a part is a Duality: two halves, one that owns *trust* and one that owns
*information*. A part acts only while both halves certify it. Nothing else is said about what a part is made of. One rule sets the
tone for everything after it: from trust nothing can be derived about information except that the information exists.

**Reading (I.1).** Read trust as *that something is* and information as *what it is*. Then "existence" is the trust half alone: a
yes or no, with no content. In mathematics the cleanest object of this kind is a **positive weight**: a number that says a
configuration counts, and says nothing about what the configuration looks like. A system exists when its total weight is positive.
**[reading]**

**Why it is a good reading.** In the first three problems the first step is exactly such a statement:

| | "Something exists" |
|---|---|
| Yang-Mills | the lattice weight e^{-S} is positive, so the partition function Z is positive |
| GRH | a pairing of test functions (Weil's explicit-formula pairing) is non-negative |
| P vs NP | a formula is satisfiable iff its count of satisfying assignments is positive (SAT iff #SAT > 0) |

**What Part II makes of it.** Positivity is the first link of the common chain (II.8; the link itself is II.9). It is the input of every construction that
follows, and it is the step that is hard in two of the first three problems.

---

## I.2 G0, the ground

**DMP.** The rules of DMP are checked by two independent witnesses. But the first two witnesses cannot be checked by anyone: somebody
has to trust them first. DMP calls that first act the *minting* and its source **G0**, the ground. G0 is "stated, not derived". Every
later standing descends from it. A system that cannot be traced back to a G0 is not part of the system.

**Reading (I.2).** G0 is the definition of the system: the action and the gauge group for Yang-Mills; the explicit formula and its
test functions for GRH; the axioms and the proof rules for P vs NP. Everything is derived from G0, and G0 itself is not. In particular,
the positivity of I.1 is either built into G0 by construction, or it has to be proved. **[reading]**

**Why it matters for the paper.** This is the single sharpest difference between the first three problems:

* In Yang-Mills positivity is part of G0. The weight e^{-S} is positive and local, so reflection positivity follows by construction
  (II.9).
* In GRH positivity is *not* part of any known G0. Weil's pairing is non-negative exactly when GRH holds. Building a G0 that makes
  it non-negative by construction is the open step (Part V).
* In P vs NP, positivity of the count is the question itself: whether the formula has a satisfying assignment.

**What Part II makes of it.** None of the tools of Part II creates positivity. They all start from it (II.16).

---

## I.3 The existence boundary (DB)

**DMP.** A boundary *contains* information when no part beyond it is trusted for any act on that information. Nothing crosses a
containing boundary. In the physical reading the author calls such a boundary an **existence boundary**, a DB. Three statements
about a DB carry most of the weight of this paper:

1. Only existence crosses a DB; information that would cross is lost.
2. Every layer has its own Duality, so the inside of a DB is a system of its own.
3. Anything that crosses a DB is re-attached to a new G0, and "anything not compatible with the encoder in the DB is lost"
   (the author, 2026-11-23).

**Reading (I.3).** A DB is a box together with its outside. "Only existence crosses" says the box sees its outside only through a
boundary condition. "What the encoder cannot carry is lost" says the passage across the boundary is a **lossy channel**: a
re-encoding into a coarser description, which can only forget. Every renormalisation step, every conditioning on an outside, and
every transfer step of a Markov chain is such a channel. **[reading]**

**What Part II makes of it.** Data processing (II.12): a channel never increases the distance between two states, and a channel that
loses something contracts it by a factor eta < 1. The same channel applied n times contracts by eta^n. That one inequality is the
engine of the Yang-Mills reduction and of the sampling side of P vs NP.

---

## I.4 Acts and remnants

**DMP.** An *act* is anything done: a message, a read, a write, a decision. Every act leaves a *record*, written at the act, readable
in full by every witness of it, and outliving the act. What an act leaves behind is its **remnant**.

The author adds two statements about remnants that this paper uses.

* **A contradiction is excised at once.** A contradictory statement is neither existence nor non-existence; it is a disagreement at
  G0. It is removed immediately, and the only remnant is the statement "it does not exist".
* **The act carrier loses nothing.** The author's example is the photon: it exists only between the event that emits it and the event
  that absorbs it, it carries one quantum, and when it delivers its act nothing is left over.

**Reading (I.4).** The first statement is proof by contradiction, read as a process. Assuming A and deriving a contradiction leaves
one remnant: not-A. In propositional logic the remnant is literal: a refutation, a derivation of the empty clause, is the certificate
that no assignment satisfies the formula. The second statement is a **conservation law**. A certificate passes from one act to the
next without loss exactly when it is carried by a conserved quantity. **[reading]**

**What Part II makes of it.**

* The remnant of a contradiction is a refutation, and every unsatisfiable formula has one (refutation completeness of tree-like
  resolution; the refutation can be exponentially long) **[Lean]** (`Proof/Complete.lean`, `refutable_iff`).
* The carrier is a conserved flux. In propositional proof (the Tseitin parity) a Gauss law holds mod 2: the parity of the true
  edges at the vertices of a region equals the parity of the true edges on its boundary, whatever happens inside **[Lean]**
  (`Proof/Crossing.lean`, `gauss`). In the plaquette layer of Yang-Mills (the centre flux, a Z/2 cochain) the Lean facts are
  counting ones: for a closed cochain the flux is the same seen from inside and from outside, and a flux cell has a sheet plaquette
  in the box **[Lean]** (`Crossover/Dichotomy.lean`, `cob_restrict_eq_cob_restrict_compl`; `Crossover/FluxRate.lean`,
  `exists_sheet_of_flux`). That conserved flux cannot be screened is the reading behind the second branch of the dichotomy (II.14)
  **[reading]**.

I.9 sharpens the first statement of this section: excision happens at transmission, and only the remnant tail is kept.

---

## I.5 The ODP: pressing, then minting

**DMP.** The **ODP**, the Oscillon Degradation Protocol, is the author's account of how a G0 finds its rules. G0 knows only how to
exist; its first act must be to find out how to act. So the "perfect duality" oscillates and decays until it reaches a stable
definition of existence, "because there MUST be a right one, because it exists" (the author, 2026-10-28).

In the protocol this happens in two phases.

* **Pressing.** A configuration is run as a rehearsal until its definition of existence is complete and its configuration hash
  matches. A pressed system is "out of spec", never "proven": the pressing is a rehearsal of the real rule, not a weaker form of it.
* **Minting.** Only a configuration that has passed its pressing is minted, and minting goes together with the **WHKs**, the White
  Hole Keys: "the entire content of creation, from which each part can derive the other" (the author, 2026-11-23). In DMP these are
  the naked duality, the quantum and the tick, together with the gap they establish.

**Reading (I.5).** Pressing is the scale-by-scale construction of a theory until one finite check passes; minting is the mechanical
production of everything else from that check. **[reading]** The reading has an exact counterpart in Yang-Mills, where the two
phases are separated in the proof:

* pressing: renormalise from the lattice spacing up to one physical scale, until a finite, local contraction condition holds in one
  box (the one-box statement, Part IV) **[open]**;
* minting: from that certificate, obtain a mass gap, as limit points of the finite-volume correlations and for the lattice
  theory **[Lean]** (`OS/GapLoc.lean`, `Assembly.lean`; conditional on the stated open inputs, Part IV; these files need no
  infinite-volume Hilbert space). The abstract reconstruction of a Hilbert space and a positive transfer operator from a positive
  form is II.9.1 **[Lean]** (abstract; its link to the spectral side is open, II.10.2).

The WHKs also have an exact counterpart. Pure Yang-Mills has no free dimensionless parameter. The bare coupling and the lattice
spacing combine into one scale, Lambda (dimensional transmutation), and every physical quantity is a pure number fixed by the group,
times a power of Lambda, where the continuum theory exists (its existence is the open problem of Part IV). From the group and any one of {the tick with its coupling, Lambda, the gap}, all the others follow.
**[classical]**

**What Part II makes of it.** The split "one finite certificate, then mechanical production" is the shape of every theorem in II.12:
a column sum below one at one scale implies decay at every larger scale.

---

## I.6 The quantum of assertion and the tick

**DMP.** An act is never infinitely small. The author: "The quantum of assertion is given along with the tick frequency at G0, so the
rate is already part of any well constructed box." The quantum and the tick also set a floor: "The loss associated with that smallest
act is a universal error bar."

**Reading (I.6).** That the quantum and the tick give a floor is a **[reading]**; two precise statements stand behind it, each
   with its own mark.

1. **A quantized measure arrives; a real one may not.** A process that lowers a natural number at every step stops after finitely
   many steps. A process that lowers a real number at every step may approach a limit forever (the witness is x -> (x + 1)/2 started at 2). **[Lean]** (`Native/Method.lean`,
   `fixed_after` and `real_never_arrives`).
2. **A finite box has a rate per tick.** In a finite box with a compact group and a bounded action, the law of the box given any
   outside has a density bounded below, so one step of the dynamics contracts by a definite factor, whatever the outside
   (Doeblin's condition). The contraction theorem is **[Lean]** for abstract finite stochastic kernels (`Mixing/Doeblin.lean`,
   `contracts_of_doeblin`); the lower bound for the Wilson box is **[paper]** (`PREP.md`, "Three answers", (a)). What the quantum does *not* give by itself is
   control of the sum over many neighbours, nor survival of the rate as the tick shrinks. That is exactly what is open in Yang-Mills
   (Part IV, and II.12 for the precise limit).

The universal floor became a project rule for measurements: every error bar is the larger of the statistical floor and the
resolution floor 1/T, with T the time extent actually observed (the time-energy resolution). **[paper]** (rule adopted
2026-11-23; `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/ONEBOX-CHECK.md`, section 7).

---

## I.7 Existence = non-existence + 1

**DMP.** The author's shortest statement: existence is at least non-existence plus one, "given by the simple fact that existence has
to also describe what does not exist, in addition to everything else" (2026-11-23). A boundary case belongs to it: with no coupling
at all there is nothing to assert, and the "+1" disappears.

**Reading (I.7).** Three exact statements share this shape. **[reading]** for the identification; the statements themselves are:

* **Set theory.** A description of all parts of a set includes the empty part, and Cantor's theorem makes it strictly larger than the
  set. In von Neumann's construction 0 = {} and 1 = {0}: the first thing that is not nothing is "a set containing nothing".
  **[classical]**
* **The strict flip bound.** For the SU(2) Wilson action at every coupling beta != 0, in every periodic L^3 x T box with T even and every twist position, the
  twisted partition function is strictly smaller than the untwisted one: Z_tw < Z **[Lean]** (`Flip/Strict.lean`, `su2_Ztw_lt_Z`).
  At beta = 0 they are equal, matching the boundary case.
* **A strict sign gives a rate at the self-dual point.** If 0 < Z_tw < Z, then the twist free energy or the electric free energy is
  at least log(1 + sqrt 2), about 0.881 **[Lean]** (`Crossover/HandOver.lean`, `log_one_add_sqrt_two_le_max`). A strict
  inequality with no rate still forces a definite rate in one of two dual channels. This is the clearest case in the paper of a DMP
  statement turning into a number (II.13).

**2 + 2 = 5, and the essence.** The first author reads 2 + 2 = 5, through DMP, as a unique impossibility on which non-existence
can be based. The exact part is one kernel evaluation: over the natural numbers `decide` refutes 2 + 2 = 5, a certified "it does
not exist" with no assumption behind it **[Lean]** (`ETM/Essence.lean`, `two_add_two_ne_five`). Read through error bars the same
sum is possible: at a resolution of one unit, 2.4 reads as 2 and 2.4 + 2.4 = 4.8 reads as 5, so the rounded sum is off by at most
one unit, the "+1" of this section **[classical]** for the arithmetic, **[reading]** for the tie (claim I.7e). His essence line
carries it to the end: **2 + 2 ? 5 ? 4 ? 0 ? 1 ? SU(5) = 1.5**. Only the last sign is an equation, so only 1.5 is assumed; every
"?" is a question to be decided from the definition of 1.5 **[reading]** (claim I.7e). The exact part is sharp. 1.5 = 3/2 exists in
a commutative ring exactly when 2 is a unit, and then each of the four ring links 2 + 2 ? 5, 5 ? 4, 4 ? 0 and 0 ? 1 is equivalent to
0 = 1: one bit decides them all, the same way. They all hold in the ring with one element, where in Z/1 the whole chain is one
`decide`, and they all fail in every other ring where 1.5 is defined **[Lean]** (`essence_decided`, `essence_decided_subsingleton`,
`essence_zmod_one`, `essence_iff_subsingleton`; Mathlib's `subsingleton_iff_zero_eq_one`). Without 1.5 the link 4 ? 0 splits off:
in Z/2, where 2 is not a unit, 4 = 0 holds and 0 = 1 does not **[Lean]** (`four_eq_zero_without_half`) (claim I.7d). The first
author reads that link, 4 ? 0, as O1 itself, the one step that has to be supplied from outside the chain, by the confinement
coupling positivity **[reading]** (claim I.7e). Care point: the Lean facts are about rings and say nothing about the Wilson measure;
O1 stays the one open step. So, once 1.5
is given, the chain names exactly one ring, the zero ring, where existence and non-existence coincide: the one box with no outside
**[reading]**. The last link is the first author's tie to the rest of the paper: SU(5), whose 5 = 3 + 2 holds the Standard Model
group as its Z_6 quotient (X.3, **[Lean]**), set equal to 1.5 = 3/2, the ratio of the start's primes and the certificate's reading
(III.4.4) **[reading]** (claim I.7e).

A last reading belongs here because Part IV uses it: **"mass gap = the arrow of causality exists"** (the author, 2026-11-22). The
transfer matrix of a reflection-positive theory is a positive contraction. A gap means that, after one unit of time 1/m, every
correlation with the past has shrunk by 1/e: a built-in clock. Without a gap correlations still fade, but only as a power law, with
no intrinsic tick. **[reading]** on the classical spectral fact of II.10.

---

## I.8 DMP as an existence linter

**DMP.** The author's one-line description of DMP: it is a very well defined *existence linter*. A linter checks a text against a
rule set and says nothing about what the text means. The author reads Gravity, the repository that holds the machine-checked
evidence, as the linter, and DMP as the universally readable rule set that is its passing condition. Gravity and DMP sit at one
node of the root chain, and the author reads them as keeping each other honest **[reading]**. The pin itself runs one way: Gravity
holds a pinned copy of DMP and checks its hash, while DMP, in its own words, "depends on nothing" and holds no copy of anything else
(`vendor/dmp/00-preamble.md`, "The root chain").

**Reading (I.8).** Existence, in the sense of I.1, is what the linter passes. A statement exists in the system when it is
constructed, by the kernel, from DMP's pinned sentences and rests on nothing else. Whatever cannot be so constructed is not part of
the system (I.2). **[reading]** (claim I.8a)

**The exact counterpart.**

* **Gravity's check passes only when** the pinned copy of DMP matches its recorded hash; the repository needs nothing that its one
  setup file does not list; no source file of the evidence chain (`evidence/`) uses an escape hatch (`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
  `implemented_by`, `extern`); the Lean build of that chain succeeds; and the kernel's axiom report for each of its theorems lists only Lean's three
  standard axioms (the check does not cover `docs/mass-gap/formal`). **[paper]** (read from `evidence/tools/check.sh` and
  `tools/check-pin.sh`; the pin check and the evidence build pass at the release commit, II.7) (claim I.8b)
* **The arsenal has the same shape at small size** (II.6): its lint is the linter, and "Mathlib v4.34.0 only, no escape hatch, an
  open part only as a named R136a1 hypothesis" is its passing condition. **[paper]** (claim I.8c)
* **The root chain pins one way.** Gravity holds a pinned copy of DMP (`vendor/dmp/PIN`, hash checked by `tools/check-pin.sh`);
  DMP depends on nothing and pins nothing (`vendor/dmp/00-preamble.md`). That the two keep each other honest is the author's reading
  of the shared node. **[paper]** for the pin; **[reading]** for the mutual honesty (claim I.8d)

**Three care points.**

1. **A linter certifies form, not content.** A passing result says that every statement is soundly constructed from what DMP
   states. It does not say that DMP's sentences describe the world. **[paper]** (claim I.8e)
2. **A linter cannot certify its own passing condition.** A consistent theory strong enough for arithmetic cannot prove its own
   consistency **[classical]** (Goedel II; claim I.8h). That is why the two nodes must keep each other honest. It is also why one assumption is
   left that neither can lint: that the system runs. This is the assumption Part III calls O1 in each card's terms. **[reading]** for
   the identification (claim I.8f)
3. **"Universally readable" holds for the form.** The evidence is plain text and Lean, checkable by anyone with the pinned
   toolchain. "Universal superset" is a reading. **[reading]** (claim I.8g)

**What Part II makes of it.** The linter's rule set is the form layer (II.1 to II.5) plus the arsenal's gate (II.6). The
unlintable assumption is the open step of each card (Part III, section 4).

**The one-box test.** The test itself, a box with one command at one shared gate and a marker per step, is Part II's one-box test (II.4).

---

## I.9 Excision at transmission

**DMP.** A part answered **R136a1** is outside the system, whatever it is. Nothing else needs to be proved about it. In DMP this is
always a DMP-complete answer: it is the other option an act collapses back on.

**Reading (I.9).** I.4 said that a contradiction is excised at once and leaves only "it does not exist". The author sharpens the
statement, and the operative word is *transmitted*. The claim is about what crosses the gate, not about what a sender may compose. A
wrong act never crosses: at the gate it is answered R136a1, so it is outside. What stays inside is only its **remnant tail**: the
record that an excision happened. IM's verifier counts every refusal without content, as the notes state (DMP chapter 04, the refusal log), so the
count is the assertion of the excision and carries none of the excised information. **[reading]** (claim I.9a)

**The exact counterpart.** In the arsenal the same move is `Arsenal.R136a1`: the part is named and stays outside every proof, and
only the name remains. It is the statement taken as a named hypothesis, never an axiom, so every declaration still rests on the
three standard axioms. **[Lean]** (`im` repository, `arsenal/Arsenal/R136a1.lean`, `R136a1`, `R136a1.out`) (claim II.6.2)

**Care point.** The gate excises what its checks can recognise as wrong at that tick. An act whose wrongness becomes recognisable
only later is excised at the later tick, with its tail recorded then. A later excision is a new act, never a revision of the earlier
tick. **[reading]** (claim I.9c). Part III, section 5, gives the logical side: excision decided per tick, and why the Clay
statements cannot be excised as a class.

---

## I.10 Rights tied to identity

**DMP.** The author's rule for security: tie rights to identity. If an act is allowed only when it is permissible, and no wrong
information can be transmitted (I.9), then the identity has total freedom *inside* and is secure in its existence.

**Reading (I.10).** "Total freedom inside, secure at the gate" is capability security, as IM builds it, and it has one more reading.
Asymptotic freedom in Yang-Mills is free at short distance, where the coupling vanishes in the ultraviolet **[classical]** (Gross-Wilczek 1973; Politzer 1973, recalled; claim I.10g), and bound
at large distance, where the gap holds. Reading the two together: inside the box the dynamics is free, and the boundary is where it
is bound. **[reading]** (claim I.10a)

**The exact counterpart.**

* **An act passes only with both witnesses' grants.** A sentence passes the door only when both the security grant and the
  operational grant carry its kind; one grant alone never passes. **[Lean]** (`im` repository, `proof/Im/Laws.lean`,
  `Im.pass_needs_both_grants`, `Im.one_grant_never_passes`) (claim I.10b)
* **Every sentence of IM's closed grammar keeps every decidable law:** there is no sentence outside the list of 72 shapes, and each shape is
  lawful (`lawfulB`: legal kind name, kind in the table, wire round-trip); the laws over grants and paths are proved once for all
  sentences in `Laws.lean` and `Wire.lean`. **[Lean]** (`proof/Im/Closure.lean`, `Im.closure`, `Im.all_shapes_lawful`,
  `Im.space_size`, `Shape.all_complete`) (claim I.10c)
* **Behind the door a composition stays lawful.** A network built from nodes that keep the guarantee on what their door lets in
  keeps it on any input. **[Lean]** (`proof/Im/Compose.lean`, `Im.sound`, `Im.galaxy_robust`) (claim I.10d)
* **Tokens only attenuate.** An attenuated token's kinds are a subset of its parent's, and a chain of attenuations is the
  intersection of the root with its caveats, in any order. It holds by construction: attenuation is intersection with a caveat.
  **[Lean]** (IM, `proof/Im/Attenuate.lean`: `attenuate_sub`, `attenuateAll_eq`, `attenuateAll_perm`; claim I.10e)

**Care points.** (1) "Permissible" is what the grammar and the grants state, so the security is exactly as good as that
specification. (2) The gate certifies integrity and authority, not the truth of content (I.9 says what happens to what it
recognises as wrong). (3) The binding of rights to identity is as strong as the custody of the identity's key. **[reading]**
(claim I.10f)

---

## I.11 The arsenal as shared vocabulary

**The rule (the first author's).** What is content-free and used by more than one project is kept once, and used from there.

**Reading (I.11).** The arsenal in the `im` repository (`arsenal/`) is that shared place for results that need Mathlib. It holds
words that more than one part of this paper uses: `R136a1` for "outside" (I.9), and the pieces that are not about any one problem.
A project that needs a word from it **imports** the word. It never copies it. If a result could be moved there, it moves, and the
project uses it from there as a dependency. **[paper]** (a project rule, and how it is done today: `arsenal/README.md`; claims
II.6.1, II.6.4). The tool that guards it, and what it checks, are in II.6.

**A second reading of the letters.** IM is the Interstellar Medium, and that name stays. Its letters also read as **Identity
Multiplication**, and the second reading is true of what the arsenal holds: the rotation API is multiplication by a number on the
unit circle, which keeps the norm and moves only the phase; on the circle the carried mass never changes **[Lean]** (II.0c,
`cmach_lossless`), and the encoder's root is the same norm read from both sides **[Lean]** (II.2). The first author reads a second reading
that carries a meaning as itself a uniqueness, one that survives being contained **[reading]** (claim I.11b). He also reads IM as
a step up the DAG: the edge is real in the build (this project requires IM's arsenal, pinned by commit, and the package graph is
acyclic). His argument for why the link is a rotation runs in three steps. A DB lets only existence cross, and the encoder's gate
keeps the norm: both sides certify the same norm **[Lean]** (`Encoder.root`; any norm-preserving map gives an encoder) and
**[reading]** for "a DB allows only this gate" (I.3). A linear gate on a line (one complex dimension) that keeps every norm is multiplication by a unit number, a
rotation **[Lean]** (II.0f; in more dimensions the norm-keeping maps are the unitary group, and that the link is a rotation there is the
first author's reading). So the link to another node, which has to pass a DB, is a rotation: the ultimate gate in the first author's words
**[reading]** (claim I.11c). The cost does not sit in the gate. In the first author's words it sits in the provability of a common root,
and that is exact: the part of the state that provably shares its root with the other side is the reflection coefficient c, and the
remainder, ||psi - conj(c) psi'||^2 = ||psi||^2 (1 - |c|^2), is exactly what the step pays **[Lean]** (`szego_remainder`). At |c| = 1
the root is fully shared and the crossing is free. On the reals the circle is just 1 and -1, so ordinary multiplication is a cost
times an identity-keeping sign **[Lean]** (II.0g): ordinary multiplication is IM as well, in the first author's words **[reading]**
(claim I.11d).

---

## I.12 The vocabulary in one table

| DMP word | Plain meaning | Reading | Precise counterpart | Part II |
|---|---|---|---|---|
| Existence (trust half) | that it is | a positive weight | Z > 0; a non-negative pairing | II.9 |
| Information half | what it is | an observable | a vector in the space built from the weight | II.9 |
| G0 | the ground, stated not derived | the definition of the system | the action, the explicit formula, the axioms | II.16 |
| DB | a containing boundary | a box with its outside | conditioning on a boundary; a lossy channel | II.12 |
| Act, remnant | what is done, what it leaves | a step; its certificate | a transfer step; a refutation; a conserved flux | II.12, II.14 |
| Act carrier | passes an act without loss | a conserved quantity | Gauss law mod 2 | II.14 |
| ODP: pressing | rehearse until the hash matches | construct up to one finite check | a column sum below 1 at one scale | II.12 |
| ODP: minting | produce from the certificate | build everything else | the mass gap from the certificate, in limits; abstract OS reconstruction | II.9, II.10 |
| WHKs | each part derives the others | no free parameter | dimensional transmutation | Part IV |
| Quantum, tick | smallest act, its rate | a rate per step | Doeblin; quantized descent arrives | II.12, II.15 |
| Existence = non-existence + 1 | always strictly more | a strict inequality | Z_tw < Z; Cantor | II.13 |
| Contradiction excised | only "it does not exist" remains | refutation | refutation completeness | II.14 |
| Mass gap | the arrow of causality exists | a clock in the transfer step | spectral gap = decay rate | II.10, II.11 |
| Existence linter | checks form, says nothing of meaning | passing means soundly constructed from DMP | the pinned check; the arsenal's lint | II.6 |
| R136a1 | the answer "outside" | excision at transmission, only the remnant tail stays | `R136a1`, a named hypothesis, never an axiom | II.6 |
| Rights tied to identity | free inside, secure at the gate | capability security | both grants needed; closure; composition | Part III |
| Arsenal | shared words, imported never copied | one place for content-free results | `arsenal/` in the `im` repository | II.6 |

Part II states each counterpart once, in its most general form.
