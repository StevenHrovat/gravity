# The paper: outline (draft 5, machine-first, relabelled 2026-11-24)

*Draft 6 (2026-11-25), the ETM as the ODP running DMP in D6, keeps this outline and adds E.0.1, the explanation mechanism, E.0.2, its
mirror the optimizer, R.11, the possibility space, R.12, the subtitle's readings, III.13 and A.2b, O1 typed as Perelman's ledger,
and Appendix E, the mechanism and the optimizer applied (`README.md`).*

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
assumption, III.64; X.64 in draft 3). The reader goes DMP, then the machine, then the one assumption and the rigid start, then the
seven problems as instances of it.

**State.** None of the seven problems is solved by this work. Each has a proved core, much of it in Lean, and exactly one named open
step; results that need the one assumption are marked conditional on it. Each open step, when it closes, changes one row of
`CLAIMS.md`, one verdict line in its part and one item of the abstract, and nothing else. Ledger (2026-11-24): 628 counted rows;
232 Lean, 125 classical, 41 external, 7 conditional, 60 paper, 22 numerical, 2 certified, 93 reading, 46 open.

## Files (draft 4, reordered 2026-11-24 after the review of the assembled paper)

| Part | Content | File | State |
|---|---|---|---|
| Front matter | title, personal note, abstract, introduction (with "The test in one page") | `draft/00-abstract-introduction.md` | reviewed (stage 3b) |
| I | DMP: the vocabulary | `draft/01-part-I-dmp.md` | reviewed; the neighbours moved to Appendix R |
| II | The machine, and the tools the problems use | `draft/02-part-II-machine.md` | reviewed |
| III | Yang-Mills | `draft/03-part-III-yang-mills.md` | reviewed |
| IV | GRH | `draft/04-part-IV-grh.md` | reviewed |
| V | P vs NP | `draft/05-part-V-pnp.md` | reviewed |
| VI | Navier-Stokes | `draft/06-part-VI-navier-stokes.md` | reviewed |
| VII | BSD | `draft/07-part-VII-bsd.md` | reviewed |
| VIII | Hodge | `draft/08-part-VIII-hodge.md` | reviewed |
| IX | GU | `draft/09-part-IX-gu.md` | reviewed |
| X | The one assumption and the rigid start, after the cards it compares | `draft/10-part-X-one-assumption.md` | reviewed, moved after the problems |
| XI | Outlook: a settling machine | `draft/11-outlook-settling-machine.md` | reviewed |
| Appendix A | Validation: Poincare, SU(N) and the rigid groups | `draft/12-appendix-a-validation.md` | reviewed |
| Appendix R | DMP readings and neighbours (linter, excision, rights, arsenal; the essence; the rotatable hash) | `draft/13-appendix-r-readings.md` | new |

The section notes below keep the draft-4 numbering of their time; the ledger's "Draft 4 labels" table maps them.

**Labels.** Relabelled once, by script (2026-11-24): every claim kept its row and got the label of its new place; the chapter
files were renamed in the same step. The draft-3 to draft-4 rule is the table "Draft 3 labels" in `CLAIMS.md`, so every draft-3
reference in older notes still resolves. Problem parts kept their inner section numbers (draft-3 III.5.6 is IV.5.6). LaTeX with one
bibliography comes after.

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

**A. The machine.** The settling machine as one object, in the order a reader needs it. (In parentheses: the draft-3 section.)

* **II.1 Running systems and the ledger** (draft 3 II.9): a step, a gate factor, a mass, the ledger law; the transport theorem. *Lean.*
* **II.2 The encoder and its half-turn** (II.10): the outside read through the same gate; the reflection coefficient. *Lean.*
* **II.3 The settle theorem and the decidability edge** (II.11): with a floor, settling within an explicit bound; without, undecidable.
  *Lean.*
* **II.4 The one-box test** (new; II.4a-c, with III.68 to III.68c): one command at the shared gate, a marker per step, DMP-complete = correct at
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
* **II.16 What the tools do not do** (draft 3 II.8): none creates positivity; the open step of each problem is where it must be
  established. **II.17 Where Part II ends** (II.15).

## Part III. The one assumption and the rigid start

Draft 3's Part X, moved up so that every problem reads as an instance of it. Its claims are III.n (draft 3 X.n).

* **III.0 How to read this part. III.1 The container**: a containing existence with free possibility space; "for every outside" as
  each card's quantifier.
* **III.2 One geometry, two edges**: GRH asks transport (existence), O1 asks decay (falsifiability). *Lean.*
* **III.3 Existence and falsifiability.**
* **III.4 Why O1 is always the open step.** III.4.1 one named slot per card; III.4.2 the running-state hypothesis; III.4.3 the
  dichotomy that makes the step decidable, and only a start that forces a floor is DMP-complete (III.70); III.4.4 the one assumption,
  stated once: its two edges, the one-box and scale certificates (III.68), GRH as a valid encoder, the rigid start and the
  encoder's language (III.69), the expected negative. *Lean + reading; open, stated.*
* **III.5 Excision and incompleteness. III.6 The tick operator and the rotatable hash. III.7 Uncertainty transported across the DB**
  (the three bridges). **III.8 What it adds up to.**

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
  Standard Model's factors as the rigid ones (pointing to III.4.4 and Appendix A.5).

## Part XI. Outlook: a settling machine

The first author's concept of a DMP-native general intelligence, tied to the settle theorem (II.3) and the one-box test (II.4).
*reading*, with its one critical link Lean. Adds no claim to the problems.

## Appendix A. Validation: Poincare, SU(N) and the rigid groups

A.0 to A.2 Perelman's proof as a ledger; A.3 Poincare for SU(N): true for N <= 3 in both categories (Wang 2021), false from N = 4
(A.3j, A.3k); A.4 the Navier-Stokes statement side by side; A.5 the rigid groups: complex representations, the U(1) gate and its
two hidden witnesses, Sp(2) strongly rigid, G2 with exactly two structures and one open test (A.5i to A.5r). *external + paper + classical + open.*

---

## Where the draft most needs the owner's input

1. **How much DMP to quote, and in whose voice.** Unchanged from draft 1.
2. **Scope of the title.** The title names the problem type; the abstract and Part VI treat both P vs NP (the sampling side) and NP vs
   coNP (proof complexity). Whether the P vs NP half stays in scope.
3. **O2-O4 for Yang-Mills.** Adopt the external construction's field notion (O3 becomes an audit item) or keep our own objects.
4. **GRH framing.** Beyond Dirichlet (where the positivity route would be new) or an independent route for Dirichlet.
5. **WHKs vs WKH.** The paper uses WHK as the owner asked; the DMP texts are unchanged.
6. **The personal note.** It still says "One thing led to three"; the paper now covers seven problems.
7. **The box for GRH, P vs NP, BSD, Hodge and GU.** *Written 2026-11-24:* every card is a box in the test (`ETM/CardBox.lean`), each
   with its ticks named (scales, restrictions, primes, codimensions, labels); the owner may refine the reading of each gate factor.

**Answered on 2026-11-24** (kept for the record): O1's final form (F_e(L) - 2c(L) > log mu_4, the excess act included) and its one
Lean form (`FineOneBox`, now the Yang-Mills instance of the one-box test); the annealed-to-quenched step (not needed in the per-outside
form, IV.5.7, Lean); GU's checkable consequence (uniform charge quantisation, X.5f); non-triviality and DMP-completeness (the lower
edge in the one assumption, DMP-complete = runs on DMP, Navier-Stokes the expected negative).
