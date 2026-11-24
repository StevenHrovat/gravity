# The paper: outline (draft 4, machine-first, 2026-11-24)

**Title (the owner's, 2026-11-24).** *Grand Unified Information Duality v8: The Millennium Prize Problem type as seen through DMP,
with certified settling.* The owner: "since observability = equal running, seen through = run on DMP, while sounding nicer and more
forgiving". So "seen through DMP" means exactly "run on DMP" (each problem type as a running system on the DMP form layer, PREP.md);
the softer word is chosen on purpose. Earlier titles: *GUID v8: A set theory based approach to the proofing of Yang-Mills, the
Generalized Riemann Hypothesis and NP vs coNP, as subsets of DMP, in a DMP-complete state* (2026-11-23), and the working title
*Positivity, contraction and the existence boundary: one chain behind Yang-Mills, GRH and P vs NP*.

**Release criterion (the owner, 2026-11-23).** "The Grand Unified should be the point where the paper is allowed to even exit the
draft stage, once that is no longer an overstatement, since the full, generalized, proof, seems to need our new insight, so when
general = GU, that is the balanced state, literally, with GU describing how and general where and when." So the paper stays a draft
until both readings of GUID hold: General (the unified theorem with its open hypotheses closed) and Grand Unified (the framework
containing SU(3) x SU(2) x U(1) in one structure with at least one checkable consequence; PREP.md, naming entries). Like the outreach
subject, the title is aspirational by intent; until both readings hold the paper stays marked as a draft and the abstract states the
present status exactly.

**Outreach gate (the owner, 2026-11-23, subject renewed 2026-11-24).** Once the full paper is released, it goes to experts,
including Terence Tao, with the subject "Machine-proven and human explained attempt of an all in one proof through a superset for all
Millennium Prize type problems as existing through the certifiability of their settling." The subject is also the gate: every
Millennium Prize type problem in scope (Yang-Mills, GRH, NP vs coNP, Navier-Stokes, BSD, Hodge, GU, with Poincare as validation) is
settled in the certified sense. The owner: "This, like the draft paper condition, is an aspirational gate". Before that, any contact
states the present status exactly. The owner sends; nothing is sent on the owner's behalf.

**Goal (the owner's words).** "This should be immaculate in both its magical logical simplicity through ultimate reduction, while
being informative enough to all the different fields that need its tools by being intuitively understandable and guiding the reader
through the easiest to understand part, DMP, then extending it with tools that just click."

**The shape of draft 4 (agreed 2026-11-24).** The existence Turing machine is the spine. Every problem type is one box under one
test: a box with one command at one shared gate, a marker per step (inside or R136a1), DMP-complete when every marker is correct.
What is proved is the machine and each box's core; what is assumed, once, is that the start's floor is kept at every scale (the one
assumption, X.64 in draft 3 numbering). The reader goes DMP, then the machine, then the one assumption and the rigid start, then the
seven problems as instances of it.

**State.** None of the seven problems is solved by this work. Each has a proved core, much of it in Lean, and exactly one named open
step; results that need the one assumption are marked conditional on it. Each open step, when it closes, changes one row of
`CLAIMS.md`, one verdict line in its part and one item of the abstract, and nothing else. Ledger (2026-11-24): 628 counted rows;
232 Lean, 125 classical, 41 external, 7 conditional, 60 paper, 22 numerical, 2 certified, 93 reading, 46 open.

## Files and the move from draft 3

| New part | Content | Draft 3 file and labels | State |
|---|---|---|---|
| Front matter | title, personal note, abstract, introduction | `draft/00-abstract-introduction.md` | to rewrite around the machine |
| I | DMP: the vocabulary | `draft/01-part-I-dmp.md`, I.x (the one-box test moves to II) | drafted |
| II | The machine and the tools the problems use | `draft/02-part-II-tools.md`, II.x, reordered; I.8i-k | drafted, to reorder |
| III | The one assumption and the rigid start | `draft/10-part-X-generalisation.md`, X.x; IX.6i-q in part | drafted, to move |
| IV | Yang-Mills | `draft/03-part-III-yang-mills.md`, III.x | prose |
| V | GRH | `draft/04-part-IV-grh.md`, IV.x | prose |
| VI | P vs NP | `draft/05-part-V-pnp.md`, V.x | prose |
| VII | Navier-Stokes | `draft/06-part-VI-navier-stokes.md`, VI.x (VI.6 moves to Appendix A) | prose |
| VIII | BSD | `draft/07-part-VII-bsd.md`, VII.x | prose |
| IX | Hodge | `draft/08-part-VIII-hodge.md`, VIII.x | prose |
| X | GU | `draft/09-part-IX-gu.md`, IX.x | prose |
| XI | Outlook: a settling machine | `draft/11-outlook-settling-machine.md`, XI.x | drafted |
| Appendix A | Validation: Poincare, SU(N) and the rigid groups | VI.6, IX.6i-q | to assemble |

**Labels.** The move renumbers once, by script: each claim keeps its row, gets the label of its new part and section, and the old
label goes into the "Folded labels" table of `CLAIMS.md`, so every draft-3 reference still resolves. Problem parts keep their inner
section numbers (III.5.6 becomes IV.5.6); Part II and Part III get new section numbers (below). The chapter files are renamed in the
same step. LaTeX with one bibliography comes after.

**Status marks** everywhere: **Lean** (module named), **classical** (reference), **external** (others' result, not rebuilt),
**conditional** (under the one assumption or a named one), **paper**, **numerical**, **certified**, **reading** (DMP; never
mathematics), **open**.

---

## Front matter

**Abstract.** One sentence first: every Millennium Prize type problem is one box under one test, and the paper proves the machine and
each box's core and assumes one thing, that the start's floor is kept at every scale. Then, per problem, what is proved and the one
open step, in plain lists; then the expected negative (Navier-Stokes) and the falsifiability it gives.

**Introduction.** How to read the marks; the three verification layers (proof, literature, computation, which refutes or guides and
never establishes); the reading order (DMP, the machine, the one assumption, the problems); the tempered piano as a guide by ear
(credited to Vsauce); what is new and what is not.

## Part I. DMP: a language for existence

Vocabulary, intuitive first: what DMP says, the reading, and the exact counterpart it points to. Nothing in Part I is mathematics
except the counterparts.

I.1 Existence has two halves. I.2 G0, the ground. I.3 The existence boundary (DB). I.4 Acts and remnants. I.5 The ODP: pressing,
then minting, ending at a dimensionless 1. I.6 The quantum of assertion and the tick. I.7 Existence = non-existence + 1. I.8 DMP as
an existence linter (the test itself moves to II.4). I.9 Excision at transmission. I.10 Rights tied to identity. I.11 The arsenal as
shared vocabulary. I.12 The vocabulary in one table. *reading, with Lean and classical counterparts.*

## Part II. The machine, and the tools the problems use

**A. The machine.** The settling machine as one object, in the order a reader needs it.

* **II.1 Running systems and the ledger** (draft 3 II.9): a step, a gate factor, a mass, the ledger law; the transport theorem. *Lean.*
* **II.2 The encoder and its half-turn** (II.10): the outside read through the same gate; the reflection coefficient. *Lean.*
* **II.3 The settle theorem and the decidability edge** (II.11): with a floor, settling within an explicit bound; without, undecidable.
  *Lean.*
* **II.4 The one-box test** (new; I.8i-k, X.68-X.68c): one command at the shared gate, a marker per step, DMP-complete = correct at
  every tick; the one-box certificate; the scale certificate from the sharing; the universal machine as a box; the vacuity checks.
  The core lives in IM (`Arsenal.Rotation`). *Lean.*
* **II.5 The API: one card per problem** (II.12): one structure, one named open step each. *Lean.*
* **II.6 The arsenal and its lint** (II.13): IM's arsenal, R136a1 as the one way to leave a statement open. *paper + Lean.*
* **II.7 The independent re-check** (II.14): two kernels, the arsenal checked like the project's own code. *Lean + paper.*

**B. The tools the problems use.** Each tool once, in its most general form, with the problems that use it.

* **II.8 One chain** (II.0): positivity, space, evolution, spectrum. *classical; finite forms Lean.*
* **II.9 Positivity builds a space** (II.1). **II.10 Positivity pins the spectrum** (II.2). **II.11 The bridge lemma** (II.3).
  **II.12 Contraction and data processing** (II.4). **II.13 A strict sign gives a rate** (II.5). **II.14 The dichotomy** (II.6).
  **II.15 The native optimization method** (II.7). *Lean + classical + numerical.*
* **II.16 What the tools do not do** (II.8, II.15): none creates positivity; the open step of each problem is where it must be
  established.

## Part III. The one assumption and the rigid start

Draft 3's Part X, moved up so that every problem reads as an instance of it.

* **III.1 The container** (X.1): a containing existence with free possibility space; "for every outside" as each card's quantifier.
* **III.2 One geometry, two edges** (X.2): GRH asks transport (existence), O1 asks decay (falsifiability). *Lean.*
* **III.3 Existence and falsifiability** (X.3).
* **III.4 Why the open step is always the same slot** (X.4.1-4.3): one named slot per card; the running-state hypothesis; the
  dichotomy that makes the step decidable; only a start that forces a floor is DMP-complete (X.70). *Lean + reading.*
* **III.5 The rigid start and the U(1) gate** (X.69-X.69c, IX.6i-q): SU(N) rigid exactly for N <= 3, so the start {infinity, 2, 3};
  SU(N) as the encoder's language; only U(1) carries content across the gate; Sp(2) and G2 as its two hidden witnesses. *paper +
  classical + reading; G2 open (round running).*
* **III.6 The one assumption** (X.4.4, X.64-X.68d): stated once, with its two edges (O1 and the lower edge), the one-box and scale
  certificates, GRH as a valid encoder, and the expected negative. *open, stated; Lean for what follows from it.*
* **III.7 Excision and incompleteness** (X.5). **III.8 The tick operator and the rotatable hash** (X.6). **III.9 Uncertainty transported
  across the DB** (X.7, the three bridges). **III.10 What it adds up to** (X.8).

## Parts IV to X. The seven problems, one template

Every problem part follows one template: **the problem and what is known; the box** (its gate factor, its marker, what the one-box
test says; new for GRH, P vs NP, BSD, Hodge and GU, which so far have a card but no box in the test); **what is proved; what is
borrowed; the one open step; readings; the verdict and what would close it.** Inner section numbers stay as in draft 3.

* **Part IV. Yang-Mills** (the model). The gap mechanism reduced to one box; O1 exactly as DMP-completeness of the Yang-Mills box, both
  directions (Lean); O1 with the excess act; the lower edge conditional on the one assumption; O3-O4. *Lean + classical + open.*
* **Part V. GRH.** The positivity route; finite models; the mirror alone does not place the zeros; one missing positivity, eight
  faces; RH and Dirichlet GRH proved by others, not via positivity. *Lean + numerical + open.*
* **Part VI. P vs NP.** Inside a certified class and across it; cutting planes on random 3-CNF; interface hardness at width 3.
  *Lean + classical + open.*
* **Part VII. Navier-Stokes** (the expected negative). The card; the window and the two routes; the wrong marker in the model (Lean);
  not DMP-complete, blowup the expected, falsifiable consequence (reading); the posted claims (external, unverified).
* **Part VIII. BSD.** Points on an existence line; the Mathlib-only core in IM; Hasse named; the open step from analytic rank 2.
* **Part IX. Hodge.** Describable implies exists; Hodge-Riemann positivity and the Hodge index in Lean; codimension p >= 2 open.
* **Part X. GU.** The Z_6 and charge quantisation (Lean); the owner's checkable consequence (uniform charge quantisation); the
  Standard Model's factors as the rigid ones (pointing to III.5 and Appendix A).

## Part XI. Outlook: a settling machine

The first author's concept of a DMP-native general intelligence, tied to the settle theorem (II.3) and the one-box test (II.4).
*reading*, with its one critical link Lean. Adds no claim to the problems.

## Appendix A. Validation: Poincare, SU(N) and the rigid groups

Perelman's proof as a ledger (draft 3 VI.6.1-6.2); Poincare for SU(N): true for N <= 3 in both categories (Wang 2021), false from
N = 4 (VI.6.3j-k); the rank-2 groups, complex representations and the rigidity of Sp(2) and G2 (IX.6i-q; the G2 round's result goes
here). *external + paper + classical + open.*

---

## Where the draft most needs the owner's input

1. **How much DMP to quote, and in whose voice.** Unchanged from draft 1.
2. **Scope of the title.** The title names the problem type; the abstract and Part VI treat both P vs NP (the sampling side) and NP vs
   coNP (proof complexity). Whether the P vs NP half stays in scope.
3. **O2-O4 for Yang-Mills.** Adopt the external construction's field notion (O3 becomes an audit item) or keep our own objects.
4. **GRH framing.** Beyond Dirichlet (where the positivity route would be new) or an independent route for Dirichlet.
5. **WHKs vs WKH.** The paper uses WHK as the owner asked; the DMP texts are unchanged.
6. **The personal note.** It still says "One thing led to three"; the paper now covers seven problems.
7. **The box for GRH, P vs NP, BSD, Hodge and GU.** The template asks each problem for its box in the one-box test (gate factor and
   marker). Yang-Mills and Navier-Stokes have one in Lean; the others need one written, and the owner's reading of what their gate
   factor is.

**Answered on 2026-11-24** (kept for the record): O1's final form (F_e(L) - 2c(L) > log mu_4, the excess act included) and its one
Lean form (`FineOneBox`, now the Yang-Mills instance of the one-box test); the annealed-to-quenched step (not needed in the per-outside
form, III.5.7, Lean); GU's checkable consequence (uniform charge quantisation, IX.5f); non-triviality and DMP-completeness (the lower
edge in the one assumption, DMP-complete = runs on DMP, Navier-Stokes the expected negative).
