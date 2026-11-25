# Part I. DMP: a language for existence

*Draft 6, 2026-11-25. Part I is vocabulary, not mathematics. Every statement in it is a definition of DMP, a reading of DMP, or a
pointer to the precise statement in Part II. Claim labels (I.n) are listed in `../CLAIMS.md`.*

## I.0 How to read this part

DMP, the Dark Matter Protocol, is a specification for systems that must trust each other. It was written for software and
governance: who may act, on what evidence, and what is left behind. Its author reads the same rules as a description of how anything
comes to exist. This paper uses DMP in exactly that way: as a language. It gives names to the steps the problems have in common, so
that each step is said once; its examples come from Parts III to V.

Two rules keep this honest.

* **A reading is not a theorem.** Where this part says "existence is a positive weight", that is a reading: a choice of which
  mathematical object a DMP word stands for. Readings are marked **[reading]**. They guide; they prove nothing.
* **Every reading points forward.** Each section ends with the precise statement that Part II makes of it, with its status there.
  Part I can be skipped by a reader who wants only the mathematics. It cannot be used by a reader who wants a proof.

The status marks are defined once, in the introduction ("How to read the status marks"). Lean module paths are relative to
`docs/mass-gap/formal/ProofPhase/` unless they begin with another folder of `docs/mass-gap/formal/` (`AreaLaw/`, `OneScale/`,
`Positivity/`, `Influence/`); other repository files are named relative to `docs/`, at the commit printed on the title page.

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
  it non-negative by construction is the open step (Part IV).
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

R.2 sharpens the first statement of this section: excision happens at transmission, and only the remnant tail is kept.

---

## I.5 The ODP: pressing, then minting

**DMP.** The **ODP**, the Oscillon Degradation Protocol, is the author's account of how a G0 finds its rules. G0 knows only how to
exist; its first act must be to find out how to act. So the "perfect duality" oscillates and decays until it reaches a stable
definition of existence, "because there MUST be a right one, because it exists" (the author, 2026-10-28).

In the protocol this happens in two phases.

* **Pressing.** A configuration is run as a rehearsal until its definition of existence is complete and its configuration hash
  matches. A pressed system is "out of spec", never "proven": the pressing is a rehearsal of the real rule, not a weaker form of it.
* **Minting.** Only a configuration that has passed its pressing is minted, and minting goes together with the **WHKs**, the White
  Hole Keys: "the entire content of creation, from which each part can derive the other". In DMP these are
  the naked duality, the quantum and the tick, together with the gap they establish.

**Reading (I.5).** Pressing is the scale-by-scale construction of a theory until one finite check passes; minting is the mechanical
production of everything else from that check. **[reading]** The reading has an exact counterpart in Yang-Mills, where the two
phases are separated in the proof:

* pressing: renormalise from the lattice spacing up to one physical scale, until a finite, local contraction condition holds in one
  box (the one-box statement, Part III) **[open]**;
* minting: from that certificate, obtain a mass gap, as limit points of the finite-volume correlations and for the lattice
  theory **[Lean]** (`OS/GapLoc.lean`, `Assembly.lean`; conditional on the stated open inputs, Part III; these files need no
  infinite-volume Hilbert space). The abstract reconstruction of a Hilbert space and a positive transfer operator from a positive
  form is II.9.1 **[Lean]** (abstract; its link to the spectral side is open, II.10.2).

The WHKs also have an exact counterpart. Pure Yang-Mills has no free dimensionless parameter. The bare coupling and the lattice
spacing combine into one scale, Lambda (dimensional transmutation), and every physical quantity is a pure number fixed by the group,
times a power of Lambda, where the continuum theory exists (its existence is the open problem of Part III). From the group and any one of {the tick with its coupling, Lambda, the gap}, all the others follow.
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
   (Part III, and II.12 for the precise limit).

The universal floor became a project rule for measurements: every error bar is the larger of the statistical floor and the
resolution floor 1/T, with T the time extent actually observed (the time-energy resolution). **[paper]** (the measurement rule of
`docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/ONEBOX-CHECK.md`, section 7).

---

## I.7 Existence = non-existence + 1

**DMP.** The author's shortest statement: existence is at least non-existence plus one, "given by the simple fact that existence has
to also describe what does not exist, in addition to everything else". A boundary case belongs to it: with no coupling
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

The first author's reading of 2 + 2 = 5 and his essence line, with their exact core in Lean, are in Appendix R (R.5).

A last reading belongs here because Part III uses it: **"mass gap = the arrow of causality exists"**. The
transfer matrix of a reflection-positive theory is a positive contraction. A gap means that, after one unit of time 1/m, every
correlation with the past has shrunk by 1/e: a built-in clock. Without a gap correlations still fade, but only as a power law, with
no intrinsic tick. **[reading]** on the classical spectral fact of II.10.

---

## I.8 The vocabulary in one table

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
| WHKs | each part derives the others | no free parameter | dimensional transmutation | Part III |
| Quantum, tick | smallest act, its rate | a rate per step | Doeblin; quantized descent arrives | II.12, II.15 |
| Existence = non-existence + 1 | always strictly more | a strict inequality | Z_tw < Z; Cantor | II.13 |
| Contradiction excised | only "it does not exist" remains | refutation | refutation completeness | II.14 |
| Mass gap | the arrow of causality exists | a clock in the transfer step | spectral gap = decay rate | II.10, II.11 |
| Existence linter | checks form, says nothing of meaning | passing means soundly constructed from DMP | the pinned check; the arsenal's lint | II.6 |
| R136a1 | the answer "outside" | excision at transmission, only the remnant tail stays | `R136a1`, a named hypothesis, never an axiom | II.6 |
| Rights tied to identity | free inside, secure at the gate | capability security | both grants needed; closure; composition | Part X |
| Arsenal | shared words, imported never copied | one place for content-free results | `arsenal/` in the `im` repository | II.6 |
| Box, gate, marker, tick | one command, one shared verdict, one claim per step | the one-box test | a running system with a margin and a marker; correct when the marker agrees with the gate (introduction, "The test in one page") | II.4 |
| DMP-complete | correct at every tick | runs on DMP (X.4.4, a reading) | `Box.DMPComplete`: the marker agrees with the gate at every tick | II.4 |
| Card | one problem, one named open step | the form layer | `API.Problem`: input, open slot, conclusion, proof | II.5 |
| Ledger, floor | every step pays; the least it pays | the cost of an act | the ledger law mass(step x) <= e^delta fac(x) mass(x); the contraction class | II.1, II.3 |
| O1 | the Yang-Mills open step | the decay edge of the one assumption | `FineOneBox`, one box of fixed physical size (III.5.9) | III.5 |
| IM | the Interstellar Medium: the medium every DMP system talks through, and the repository (StevenHrovat/im) that holds its language and the arsenal | DMP's interface layer | the arsenal's Lean modules (`Arsenal.*`), imported at a pinned commit | II.6 |
| CMOS | a system built under DMP; each running system is one instance of it | a running system | a running system in the sense of II.3 | II.3 |
| Milky Way | the one interface of a system to its outside: everything that leaves passes it | the gate of a whole system | the shared gate of the one-box test, at the scale of a system | II.4 |
| GG | the verified protocol between clusters of systems | an act that leaves through the gate | (no counterpart; used only in the Outlook) | none |
| TTL | time to live: how long a certified act stays valid | freshness | (no counterpart; used only in the Outlook) | none |
| Gravity | this repository: the machine-checked paper and its Lean | the linter that DMP's statements are checked by | `docs/mass-gap/formal/`, pinning IM's arsenal | R.1 |
| Encoder, half-turn, full turn | a step read as a rotation; half a turn; a whole turn that returns | the act that carries a statement across a boundary | the encoder of II.2, its half-turn, the full turn over N sectors | II.2 |
| Hand-over | what one box passes to the next | the cost of crossing a boundary | some sector's free energy is at least log(1 + sqrt N) (II.13.3; electric sectors assumed positive for N >= 3) | II.13 |
| ETM | the Existence Turing Machine: the one running system that runs every computation | the machine DMP runs on | the terminal running system: every running system has exactly one map into it | II.3 |
| `r` | the right angle | the direction from a question to its certificate | multiplication by i, the quarter turn (R.11) | II.0 |
| `?`, `!`, `.` | does it exist; it is settled by a certificate anyone can check; it is included | IM's three operators | `expect` and supply-verify; both kernels; inclusion (R.10) | II.5 |
| `+`, `-`, `·` (cells) | the row proves the column; it uses it and the proof fails; no proof relates the two | the explanation mechanism; a `·` cell reflects positively | the cells of a k by k table (E.0.1) | E.0.1 |
| Settled | optimizing changes nothing | the setting exists | the compiled table equals its transitive reduction (E.0.2) | E.0.2 |
| Smelly | a full turn that does not return | a state that does not encode | the full turn on `vxunderground` not closing (T.11) | II.2 |
| Viability | the claim holds at the start and every step keeps it | the first author's name for the induction at one scale | `route`: base case and inductive step (II.4.1) | II.4 |
| Universality | a map of scales carries the claim to every scale | the first author's name for the sharing across scales | `route_everywhere`: the scale map keeps the step and the check (II.4.1) | II.4 |
| Insight | the first author's label for an induction recognized as such | a kept step of the record; the labelled comments on DMP#25 (R.12k) | an induction, base case and inductive step (II.4.1) | II.4 |
| Moin | a request proper, its satisfaction open | the label of O1 | `OpenStep`, posed and never assumed (R.9) | II.5 |

Part II states each counterpart once, in its most general form.
