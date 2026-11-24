# Appendix R. DMP readings and neighbours

*Draft 4. Claim labels (R.n) are listed in `../CLAIMS.md`.*

This appendix holds what no card of Parts III to IX uses: DMP's own neighbours (the linter, excision, rights tied to identity, IM's
arsenal) and two readings of the first author that are not tied to one part (the essence line and the rotatable hash). Each
section names the result it reads; the marks are those of the introduction.

## R.1 DMP as an existence linter

**DMP.** The author's one-line description of DMP: it is a very well defined *existence linter*. A linter checks a text against a
rule set and says nothing about what the text means. The author reads Gravity, the repository that holds the machine-checked
evidence, as the linter, and DMP as the universally readable rule set that is its passing condition. Gravity and DMP sit at one
node of the root chain, and the author reads them as keeping each other honest **[reading]**. The pin itself runs one way: Gravity
holds a pinned copy of DMP and checks its hash, while DMP, in its own words, "depends on nothing" and holds no copy of anything else
(`vendor/dmp/00-preamble.md`, "The root chain").

**Reading (R.1).** Existence, in the sense of I.1, is what the linter passes. A statement exists in the system when it is
constructed, by the kernel, from DMP's pinned sentences and rests on nothing else. Whatever cannot be so constructed is not part of
the system (I.2). **[reading]** (claim R.1a)

**The exact counterpart.**

* **Gravity's check passes only when** the pinned copy of DMP matches its recorded hash; the repository needs nothing that its one
  setup file does not list; no source file of the evidence chain (`evidence/`) uses an escape hatch (`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
  `implemented_by`, `extern`); the Lean build of that chain succeeds; and the kernel's axiom report for each of its theorems lists only Lean's three
  standard axioms (the check does not cover `docs/mass-gap/formal`). **[paper]** (read from `evidence/tools/check.sh` and
  `tools/check-pin.sh`; the pin check and the evidence build pass at the release commit, II.7) (claim R.1b)
* **The arsenal has the same shape at small size** (II.6): its lint is the linter, and "Mathlib v4.34.0 only, no escape hatch, an
  open part only as a named R136a1 hypothesis" is its passing condition. **[paper]** (claim R.1c)
* **The root chain pins one way.** Gravity holds a pinned copy of DMP (`vendor/dmp/PIN`, hash checked by `tools/check-pin.sh`);
  DMP depends on nothing and pins nothing (`vendor/dmp/00-preamble.md`). That the two keep each other honest is the author's reading
  of the shared node. **[paper]** for the pin; **[reading]** for the mutual honesty (claim R.1d)

**Three care points.**

1. **A linter certifies form, not content.** A passing result says that every statement is soundly constructed from what DMP
   states. It does not say that DMP's sentences describe the world. **[paper]** (claim R.1e)
2. **A linter cannot certify its own passing condition.** A consistent theory strong enough for arithmetic cannot prove its own
   consistency **[classical]** (Goedel II; claim R.1h). That is why the two nodes must keep each other honest. It is also why one assumption is
   left that neither can lint: that the system runs. This is the assumption Part X calls O1 in each card's terms. **[reading]** for
   the identification (claim R.1f)
3. **"Universally readable" holds for the form.** The evidence is plain text and Lean, checkable by anyone with the pinned
   toolchain. "Universal superset" is a reading. **[reading]** (claim R.1g)

**What Part II makes of it.** The linter's rule set is the form layer (II.1 to II.5) plus the arsenal's gate (II.6). The
unlintable assumption is the open step of each card (Part X, section 4).

**The one-box test.** The test itself, a box with one command at one shared gate and a marker per step, is Part II's one-box test (II.4).

---

## R.2 Excision at transmission

**DMP.** A part answered **R136a1** is outside the system, whatever it is. Nothing else needs to be proved about it. In DMP this is
always a DMP-complete answer: it is the other option an act collapses back on.

**Reading (R.2).** I.4 said that a contradiction is excised at once and leaves only "it does not exist". The author sharpens the
statement, and the operative word is *transmitted*. The claim is about what crosses the gate, not about what a sender may compose. A
wrong act never crosses: at the gate it is answered R136a1, so it is outside. What stays inside is only its **remnant tail**: the
record that an excision happened. IM's verifier counts every refusal without content, as the notes state (DMP chapter 04, the refusal log), so the
count is the assertion of the excision and carries none of the excised information. **[reading]** (claim R.2a)

**The exact counterpart.** In the arsenal the same move is `Arsenal.R136a1`: the part is named and stays outside every proof, and
only the name remains. It is the statement taken as a named hypothesis, never an axiom, so every declaration still rests on the
three standard axioms. **[Lean]** (`im` repository, `arsenal/Arsenal/R136a1.lean`, `R136a1`, `R136a1.out`) (claim II.6.2)

**Care point.** The gate excises what its checks can recognise as wrong at that tick. An act whose wrongness becomes recognisable
only later is excised at the later tick, with its tail recorded then. A later excision is a new act, never a revision of the earlier
tick. **[reading]** (claim R.2c). Part X, section 5, gives the logical side: excision decided per tick, and why the Clay
statements cannot be excised as a class.

---

## R.3 Rights tied to identity

**DMP.** The author's rule for security: tie rights to identity. If an act is allowed only when it is permissible, and no wrong
information can be transmitted (R.2), then the identity has total freedom *inside* and is secure in its existence.

**Reading (R.3).** "Total freedom inside, secure at the gate" is capability security, as IM builds it, and it has one more reading.
Asymptotic freedom in Yang-Mills is free at short distance, where the coupling vanishes in the ultraviolet **[classical]** (Gross-Wilczek 1973; Politzer 1973, recalled; claim R.3g), and bound
at large distance, where the gap holds. Reading the two together: inside the box the dynamics is free, and the boundary is where it
is bound. **[reading]** (claim R.3a)

**The exact counterpart.**

* **An act passes only with both witnesses' grants.** A sentence passes the door only when both the security grant and the
  operational grant carry its kind; one grant alone never passes. **[Lean]** (`im` repository, `proof/Im/Laws.lean`,
  `Im.pass_needs_both_grants`, `Im.one_grant_never_passes`) (claim R.3b)
* **Every sentence of IM's closed grammar keeps every decidable law:** there is no sentence outside the list of 72 shapes, and each shape is
  lawful (`lawfulB`: legal kind name, kind in the table, wire round-trip); the laws over grants and paths are proved once for all
  sentences in `Laws.lean` and `Wire.lean`. **[Lean]** (`proof/Im/Closure.lean`, `Im.closure`, `Im.all_shapes_lawful`,
  `Im.space_size`, `Shape.all_complete`) (claim R.3c)
* **Behind the door a composition stays lawful.** A network built from nodes that keep the guarantee on what their door lets in
  keeps it on any input. **[Lean]** (`proof/Im/Compose.lean`, `Im.sound`, `Im.galaxy_robust`) (claim R.3d)
* **Tokens only attenuate.** An attenuated token's kinds are a subset of its parent's, and a chain of attenuations is the
  intersection of the root with its caveats, in any order. It holds by construction: attenuation is intersection with a caveat.
  **[Lean]** (IM, `proof/Im/Attenuate.lean`: `attenuate_sub`, `attenuateAll_eq`, `attenuateAll_perm`; claim R.3e)

**Care points.** (1) "Permissible" is what the grammar and the grants state, so the security is exactly as good as that
specification. (2) The gate certifies integrity and authority, not the truth of content (R.2 says what happens to what it
recognises as wrong). (3) The binding of rights to identity is as strong as the custody of the identity's key. **[reading]**
(claim R.3f)

---

## R.4 The arsenal as shared vocabulary

**The rule (the first author's).** What is content-free and used by more than one project is kept once, and used from there.

**Reading (R.4).** The arsenal in the `im` repository (`arsenal/`) is that shared place for results that need Mathlib. It holds
words that more than one part of this paper uses: `R136a1` for "outside" (R.2), and the pieces that are not about any one problem.
A project that needs a word from it **imports** the word. It never copies it. If a result could be moved there, it moves, and the
project uses it from there as a dependency. **[paper]** (a project rule, and how it is done today: `arsenal/README.md`; claims
II.6.1, II.6.4). The tool that guards it, and what it checks, are in II.6.

**A second reading of the letters.** IM is the Interstellar Medium, and that name stays. Its letters also read as **Identity
Multiplication**, and the second reading is true of what the arsenal holds: the rotation API is multiplication by a number on the
unit circle, which keeps the norm and moves only the phase; on the circle the carried mass never changes **[Lean]** (II.0c,
`cmach_lossless`), and the encoder's root is the same norm read from both sides **[Lean]** (II.2). The first author reads a second reading
that carries a meaning as itself a uniqueness, one that survives being contained **[reading]** (claim R.4b). He also reads IM as
a step up the DAG: the edge is real in the build (this project requires IM's arsenal, pinned by commit, and the package graph is
acyclic). His argument for why the link is a rotation runs in three steps. A DB lets only existence cross, and the encoder's gate
keeps the norm: both sides certify the same norm **[Lean]** (`Encoder.root`; any norm-preserving map gives an encoder) and
**[reading]** for "a DB allows only this gate" (I.3). A linear gate on a line (one complex dimension) that keeps every norm is multiplication by a unit number, a
rotation **[Lean]** (II.0f; in more dimensions the norm-keeping maps are the unitary group, and that the link is a rotation there is the
first author's reading). So the link to another node, which has to pass a DB, is a rotation: the ultimate gate in the first author's words
**[reading]** (claim R.4c). The cost does not sit in the gate. In the first author's words it sits in the provability of a common root,
and that is exact: the part of the state that provably shares its root with the other side is the reflection coefficient c, and the
remainder, ||psi - conj(c) psi'||^2 = ||psi||^2 (1 - |c|^2), is exactly what the step pays **[Lean]** (`szego_remainder`). At |c| = 1
the root is fully shared and the crossing is free. On the reals the circle is just 1 and -1, so ordinary multiplication is a cost
times an identity-keeping sign **[Lean]** (II.0g): ordinary multiplication is IM as well, in the first author's words **[reading]**
(claim R.4d).

---

## R.5 The essence

**2 + 2 = 5, and the essence.** The first author reads 2 + 2 = 5, through DMP, as a unique impossibility on which non-existence
can be based. The exact part is one kernel evaluation: over the natural numbers `decide` refutes 2 + 2 = 5, a certified "it does
not exist" with no assumption behind it **[Lean]** (`ETM/Essence.lean`, `two_add_two_ne_five`). Read through error bars the same
sum is possible: at a resolution of one unit, 2.4 reads as 2 and 2.4 + 2.4 = 4.8 reads as 5, so the rounded sum is off by at most
one unit, the "+1" of this section **[classical]** for the arithmetic, **[reading]** for the tie (claim R.5b). His essence line
carries it to the end, with each "?" a question to be decided and only the last sign an equation: **2 + 2 ? 5 ? 4 ? 0 ? 1 ?
SU(5) = 1.5**. So only 1.5 is assumed, and every link is decided from its definition **[reading]** (claim R.5b). The exact part is sharp. 1.5 = 3/2 exists in
a commutative ring exactly when 2 is a unit, and then each of the four ring links 2 + 2 ? 5, 5 ? 4, 4 ? 0 and 0 ? 1 is equivalent to
0 = 1: one bit decides them all, the same way. They all hold in the ring with one element, where in Z/1 the whole chain is one
`decide`, and they all fail in every other ring where 1.5 is defined **[Lean]** (`essence_decided`, `essence_decided_subsingleton`,
`essence_zmod_one`, `essence_iff_subsingleton`; Mathlib's `subsingleton_iff_zero_eq_one`). Without 1.5 the link 4 ? 0 splits off:
in Z/2, where 2 is not a unit, 4 = 0 holds and 0 = 1 does not **[Lean]** (`four_eq_zero_without_half`) (claim R.5a). The first
author reads that link, 4 ? 0, as O1 itself, the one step that has to be supplied from outside the chain, by the confinement
coupling positivity **[reading]** (claim R.5b). Care point: the Lean facts are about rings and say nothing about the Wilson measure;
O1 stays the one open step. So, once 1.5
is given, the chain names exactly one ring, the zero ring, where existence and non-existence coincide: the one box with no outside
**[reading]**. The last link is the first author's tie to the rest of the paper: SU(5), whose 5 = 3 + 2 holds the Standard Model
group as its Z_6 quotient (IX.3, **[Lean]**), set equal to 1.5 = 3/2, the ratio of the start's primes and the certificate's reading
(X.4.4) **[reading]** (claim R.5b).

---

## R.6 The rotatable hash: the root chain closes through time

DMP and Gravity are the two repositories of the root chain. The pin runs one way: a `PIN` in Gravity records the sha256 of the
pinned copy of DMP, and the pin check turns any change of it into a failing check (`vendor/dmp/PIN`, `tools/check-pin.sh`); DMP
depends on nothing and pins nothing (`vendor/dmp/00-preamble.md`). So every pinned existence is a claim the gate can refute
**[paper]** (claim R.1d). A literal circle of hashes cannot be constructed: a file that contains its own hash, or two
files that contain each other's current hashes, is a fixed point of sha256, which no one can compute **[classical]** (by the hash's
design) (claim X.51). The first author reads the root chain as closing through time instead: each version of Gravity pins an earlier
version of DMP, and the next version of DMP is written against what Gravity checked, so the chain is a spiral of versions, one tick per
pin **[reading]** (claim R.1d). Care point: such a circle is consistent only because it never closes at one instant. A pin to the
other side's *current* commit would be the uncomputable fixed point.

The first author corrected the first wording: the hash is *rotatable*, not negatable. The hash itself is one-way **[classical]**. What
rotates is the pin: across versions the pin passes from one node to the other, a turn per tick, the same half-turn shape as the
encoder's, where two half-turns return to the start and the start is one version later **[reading]** (claim X.52). Care point: no hash
function is rotated, the roles of pinner and pinned are. The first author adds that inside the system the time-to-live of a certification
is not a separate mechanism. Every certification is re-made at each tick, against the same shared root, and never reaches back, so
the validity window of any hash is bounded by the interval between two ticks **[reading]** (claim X.53). What leaves the inside is outside
by definition, so its lifetime is the boundary's matter, not the rotation's.
