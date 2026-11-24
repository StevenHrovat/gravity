# The paper: outline (draft 3, 2026-11-24)

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
containing SU(3) x SU(2) x U(1) in one structure with at least one checkable consequence; PREP.md, naming entries). The owner has
now set the full expansion in the title (2026-11-24); like the outreach subject it is aspirational by intent, so until both readings
hold the paper stays marked as a draft and the abstract states the present status exactly.

**Outreach gate (the owner, 2026-11-23, subject renewed 2026-11-24).** Once the full paper is released, it goes to experts,
including Terence Tao, with the subject "Machine-proven and human explained attempt of an all in one proof through a superset for all
Millennium Prize type problems as existing through the certifiability of their settling." (Earlier subject, 2026-11-23: "...a three
in one proof through a superset for full YM, GRH and PvNP for a state that is considered running on the superset.") The new subject
is also the new gate: every Millennium Prize type problem in scope (YM, GRH, NP vs coNP, GU, Navier-Stokes, BSD, Hodge, with
Poincare as validation) is settled in the certified sense. The owner: "This, like the draft paper condition, is an aspirational gate". The
subject is used only in the settled state, when every word of it holds true, i.e. under the same condition as the release criterion
above. Before that, any contact states the present status exactly. The owner sends; nothing is sent on the owner's behalf.

**Goal (the owner's words).** "This should be immaculate in both its magical logical simplicity through ultimate reduction, while
being informative enough to all the different fields that need its tools by being intuitively understandable and guiding the reader
through the easiest to understand part, DMP, then extending it with tools that just click."

**State (draft 3).** None of the seven problems is solved by this work. Each card has a proved core, much of it in Lean, and exactly
one named open step; the results that need the one assumption (O1, Part X 4.4) are marked conditional on it.
The paper is built so that each open step, when it closes, changes one row of `CLAIMS.md`, one verdict line in its part and one
item of the abstract, and nothing else.

## Files

| File | What | State |
|---|---|---|
| `OUTLINE.md` | this file: structure, one paragraph per section, status per section | draft 3 |
| `CLAIMS.md` | every claim of the draft: status, source, what would upgrade it (651 counted rows) | draft 3 |
| `claims-incoming/` | the writers' rows for draft 3, as merged into `CLAIMS.md` (kept for their notes to the coordinator) | merged |
| `draft/00-abstract-introduction.md` | the owner's title and personal note; abstract and introduction | drafted (lists updated in draft 2) |
| `draft/01-part-I-dmp.md` | Part I, DMP | fully drafted |
| `draft/02-part-II-tools.md` | Part II, the tools | fully drafted |
| `draft/03-part-III-yang-mills.md` | Part III | prose (draft 2) |
| `draft/04-part-IV-grh.md` | Part IV | prose (draft 2) |
| `draft/05-part-V-pnp.md` | Part V | prose (draft 2) |
| `draft/06-part-VI-navier-stokes.md` | Part VI, Navier-Stokes, with Poincare as validation | prose (draft 3, new) |
| `draft/07-part-VII-bsd.md` | Part VII, BSD | prose (draft 3, new) |
| `draft/08-part-VIII-hodge.md` | Part VIII, Hodge | prose (draft 3, new) |
| `draft/09-part-IX-gu.md` | Part IX, GU | prose (draft 3, new) |
| `draft/10-part-X-generalisation.md` | Part X, the generalisation | prose (draft 3, rewritten) |
| `draft/11-outlook-settling-machine.md` | Outlook: the first author's concept of a DMP-native general intelligence, tied to the ETM's settle theorem | drafted (2026-11-23) |

LaTeX comes later. Status marks everywhere: **Lean** (module named), **classical** (reference), **external** (others' result, not
rebuilt), **conditional** (under a named assumption), **paper**, **numerical**, **reading** (DMP; never mathematics), **open**.

---

## Front matter

**Abstract.** States the one chain (positivity -> space -> evolution -> spectrum), then in two plain lists what is proved and what is
not, problem by problem. Status: every sentence points to a ledger row; the "not proved" list names O1-O4 (Yang-Mills), the
zero-free arithmetic Hilbert space and GRH beyond Dirichlet (GRH), the crossing and Frege lower bounds with the three barriers
(P vs NP).

**Introduction.** One idea used three times: positivity is existence. What each field's reader can take away; how to read the
marks; the three verification layers (proof, literature, computation; computation refutes or guides, never establishes); what is new
and what is not. Status: scope statements and pointers only.

## Part I. DMP: a language for existence

Vocabulary, intuitive first. Every section: what DMP says (short quote), the reading, the precise counterpart in Part II. Nothing in
Part I is mathematics except the counterparts it points to.

* **I.1 Existence has two halves.** Trust = that it is; information = what it is. Reading: existence is a positive weight; Z > 0 in
  all three problems. *reading; the Z > 0 facts classical.*
* **I.2 G0, the ground.** The first act is stated, not derived. Reading: G0 is the definition of the system. The sharpest difference
  between the problems: positivity is in G0 for Yang-Mills, equivalent to the conclusion for GRH, the question itself for P vs NP.
  *reading.*
* **I.3 The existence boundary (DB).** Only existence crosses; what the encoder cannot carry is lost. Reading: a box with its
  outside; a lossy channel. *reading; counterpart II.4 Lean.*
* **I.4 Acts and remnants.** A contradiction is excised and leaves "it does not exist" (a refutation, Lean); the act carrier passes
  an act without loss (a conservation law; Gauss law mod 2, Lean). *reading + Lean counterparts.*
* **I.5 The ODP: pressing, then minting.** Rehearse until one finite check passes, then produce; the WHKs: each part derives the
  others. Reading: construct up to the one-box certificate (open), then OS reconstruction and limits (Lean); dimensional
  transmutation (classical). *reading.*
* **I.6 The quantum of assertion and the tick.** Quantized descent arrives (Lean); a finite box has a Doeblin rate per step (Lean,
  abstract); the universal error-bar floor 1/T (project rule). *reading + Lean.*
* **I.7 Existence = non-existence + 1.** Cantor and 1 = {0} (classical); Z_tw < Z (Lean); a strict sign gives the rate 0.881 at the
  self-dual point (Lean). Mass gap = the arrow of causality exists (reading). *reading + Lean.*
* **I.8 The vocabulary in one table.** DMP word, plain meaning, reading, counterpart, section.

## Part II. The tools that click

Each tool once, most general form, a one-line "why it clicks", three applications.

* **II.0 One chain, three problems.** The table; links 2-4 are free once link 1 holds. *classical; finite forms Lean.*
* **II.1 Positivity builds a space.** Reconstruction from a positive form (GNS/OS); Lean abstract form; applications: Wilson RP
  (Lean), finite Weil criterion (Lean), heat-bath spectral measure (Lean). *Lean + classical.*
* **II.2 Positivity pins the spectrum.** Decay rate = bottom of the spectrum; gap from RP and block decay. *Lean.*
* **II.3 The bridge lemma.** Pringsheim extension (Lean, no sign needed in the core; positivity enters in the instances by Tonelli);
  instances Landau, Laplace, resolvent (Lean). What it does not give: an arithmetic positivity (open). *Lean; one open pointer.*
* **II.4 Contraction and data processing.** Composition, Doeblin, column sum < 1 gives a gap (Lean); the honest limit: per-channel
  Doeblin cannot give a column below 1 (Lean); uniformity along a homogeneous chain (classical). *Lean.*
* **II.5 A strict sign gives a rate.** The hand-over bound max(F_tw, F_e) >= log(1 + sqrt 2), sharp (Lean); what it does not give
  (annealed, one box). *Lean.*
* **II.6 The dichotomy.** Local / crossing flux / residue as a strategy (paper); exact parts: Gauss law, forced sheets, uncontained
  sheets weigh nothing, every refutation crosses, disjoint regimes (all Lean). *paper + Lean.*
* **II.7 The native optimization method.** Quantized descent arrives; pointer jumping; measured per-layer cost. *Lean + numerical.*
* **II.8 What the tools do not do.** None creates positivity; the open step of each problem is where it must be established.

## Part III. Yang-Mills: the gap mechanism reduces to one box of fixed physical size

* **III.0 What is proved and what is not.** Minting half done in Lean (conditional on stated inputs); gap mechanism reduced to one box.
  Open: **O1** F_e(L) - 2c(L) > log mu_4 = 1.91 at one box of fixed physical size, uniformly over outsides (the excess act
  included); O2 line of constant physics and non-triviality, whose scale-uniform lower edge is the one assumption's other edge; O3 continuum field theory; O4 other groups.
* **III.1 Lattice theory and positivity.** *Lean.* **III.2 Minting half**, and why the crossover needs no description of its content
  (paper). *Lean.*
* **III.3 What one box gives, and how a chain carries it.** Hand-over 0.881, forced sheet, the same law on both sides,
  superadditivity, uniformity, physical units. *Lean + classical.*
* **III.4 Why a grid is harder than a chain.** Column requirement log 8; Doeblin vanishes in the continuum; multi-sector duality
  forces nothing; a covariant frame carries nothing. *Lean + paper.*
* **III.5 Containment.** Outside absence (lemma); the container ends in long boxes; Gauss's law gives path-like influence; tube
  threshold F > log mu, which 0.881 fails in d >= 3; Bogomolny helps only outside; **O1**; care points (annealed to quenched;
  relation to F_e > 2c; which Lean input form). *Lean + classical + open.*
* **III.6 Saturation and the dichotomy.** Tick-unit floor; saturation is a consequence of O1; Tomboulis's step localised to one box;
  dichotomy (a) fails, (b) holds; Y2-Y5. *Lean + paper + open.*
* **III.7 Measured.** Small tori (passes centrally, not certified); the chain check at 16^3 (refuted, does not bear on O1); the
  universal floor; the mirror reading L sqrt(sigma) of about 1.7 to 1.8. *numerical.*
* **III.8 "It runs"** (shared with GRH). *Lean.* **III.9 Weak coupling and continuum** (O2-O4). **III.10 Readings. III.11 What would
  close it.**

## Part IV. GRH: the positivity route

* **IV.0 State.** RH and Dirichlet GRH proved in Lean by others, not via positivity (external); GRH beyond Dirichlet open; this part
  proves no case of GRH.
* **IV.1 Finite models.** *Lean.*
* **IV.2 The mirror alone does not place the zeros.** krein_off_line; Tate's local functional equations and Davenport-Heilbronn; the
  one local sign Lambda(n) >= 0 and the global one-sided bound; the bridge; the two 1/2s. *Lean + classical + open.*
* **IV.3 Measured shape.** Exact cancellation at each step; ground state on the circle; the true primes 1e-9 from the edge; all or
  nothing; no two-term bound; no place-by-place assembly (Lean); the real place alone is indefinite. *numerical + Lean.*
* **IV.4 One missing positivity, eight faces.** *open.*
* **IV.5 "It runs"**, the face shared with Yang-Mills. *Lean + open.* **IV.6 Readings. IV.7 What would close it.**

## Part V. P vs NP: inside a certified class, and across it

* **V.0 State.** Neither P vs NP nor NP vs coNP is resolved.
* **V.1 Inside the class**, now unconditional for finite systems. *Lean + classical.* **V.2 At the edge of the class.**
* **V.3 Refutations**, with the DAG-like size-width relation now in Lean. *Lean + classical.*
* **V.4 The edge: cutting planes on random 3-CNF.** Crossing forced; the majority line survives restrictions; duality floor for unit
  thresholds and its failure for weighted lines; interpolation split and creative pairs; positivity to rank only; **interface
  hardness at width 3** open. *Lean + classical + open.*
* **V.5 Native method. V.6 Open steps N1-N4. V.7 Barriers. V.8 Readings. V.9 What would close it.**

## Part VI. Navier-Stokes: the card, the claimed certificate, and Poincare as validation

Fefferman's four forms (A) to (D); the card on the API; what the form layer says about the two blowup routes, as a skeleton with no
Navier-Stokes object in it (Lean); the two posted blowup claims (external, unverified; one certificate unreleased); the one open
step; Perelman's proof of Poincare as the check of the restatement.

## Part VII. Birch and Swinnerton-Dyer: points on an existence line

BSD as a property of one Weierstrass equation over a number field; the Mathlib-only core in IM (`Arsenal.BSD`): Mordell-Weil from
weak Mordell-Weil, the true rank, the existence line, parity, point counts that run, a finite order at s = 1 from Hasse; three
classical theorems Mathlib lacks as named R136a1 parts; the card and the y^2 = x^3 - x example; the open step from order 2 on.

## Part VIII. Hodge: describable implies exists

The card; Hodge-Riemann positivity, the Hodge index as linear algebra, Weil's bound for curves, eigenvalues on the circle,
Lefschetz (1,1) (Lean); the geometry as named External slots; the open step in codimension p >= 2.

## Part IX. GU: the Grand Unified reading

Not a Clay problem: the second half of the release criterion. The Z_6 quotient inside SU(5) and charge quantisation from a compact
U(1) (Lean); the hypercharges as input; the two candidate checkable consequences, with the choice left to the owner.

## Part X. The generalisation

Draft 3 order: (1) the container: a containing existence with free possibility space, the quantifier "for every outside" of each
card; (2) one geometry, two edges: GRH and O1 ask opposite, independent bounds of one distance (Lean, `GRHToO1.lean`); (3)
existence and falsifiability; (4) why O1 is always the open step, with the one assumption stated once (4.4); (5) excision and
incompleteness; (6) the tick operator and the rotatable hash; (7) the uncertainty transport. Draft 2's text follows for reference.

One shape. A table of the sharpest open step per problem: what is proved for one unit, why it does not carry, what no duality
supplies, the hard quantifier, what measurement says, and the "it runs" form. What the act-carrier answer settled; what can and
cannot close each step; why Yang-Mills is the model; how the paper closes locally.

**The approach for the content layer (the owner, 2026-11-23).** "Exactly define the uncertainty, then transport it in a meaningful
way across a DB." Per problem, the one named bridge is stated as a precise proposition with a size:
- Yang-Mills: the electric-side deficit and the side-seam cost;
- GRH: the explicit formula's remainder between the finite model and zeta;
- NP: the lifting quantum.

Its transport across the DB obeys the ledger law, so it contracts exactly when the step pays a cost above the floor (Lean). Part X
is organised by this: where each problem's uncertainty sits, how it crosses its boundary, and why GRH (zero slack) is the case where
it crosses without damping.

**X.7 Uncertainty transported across the DB.** The transport theorem (bounded under contraction, critical at cost = floor and sharp,
sign preserved below a margin; the ledger at no fresh uncertainty) and the three bridges side by side (`three_bridges`), each under its
named running-state hypothesis R; R for the specific objects is the open step (Lean; `docs/unified/TRANSPORT.md`).

## Part XI. Outlook: a settling machine

The first author's concept of a DMP-native general intelligence: a CMOS system in IM tokens, one Milky Way gate that checks hash
and TTL before an act leaves as GG, an output rate set from outside, and total freedom inside. *reading.* Its one critical link
to this work is the ETM's settle theorem: settling within an explicit bound when every step contracts, undecidable in general.
*Lean.* Care points: the gate certifies integrity, not meaning, and must check acts, not self-reports. Placed after Part X as
an outlook; it adds no claim to the problems.

---

## Where the draft most needs the owner's input

1. **O1 in its final form.** *Answered 2026-11-24:* the headline is F_e(L) - 2c(L) > log mu_4, the excess act included and the
   familiar form shown as its seeming simplification; the one Lean form proposed is `FineOneBox` (to confirm). The notes now give two one-box criteria at one scale: the chain criterion F_e(L) > 2c(L) (HTF) and the
   tube threshold F_e(L) > log mu_4 (CONTAINMENT). The paper needs one statement, the Lean input form it corresponds to
   (`FineOneBox`, `FineOneBoxSplit`, `BlockGapBddW`), and the owner's worst-case argument for one box, stated so it can be checked.
2. **The annealed-to-quenched step.** The path expansion behind the tube threshold assumes that per-box costs multiply along a path.
   Either it becomes part of O1 or it needs its own argument.
3. **How much DMP to quote, and in whose voice.** Unchanged from draft 1.
4. **Scope of the title.** The owner's title names NP vs coNP; the abstract and Part V treat both P vs NP (the sampling side) and
   NP vs coNP (proof complexity). Whether the P vs NP half stays in scope.
5. **O2-O4 for Yang-Mills.** Adopt the external construction's field notion (O3 becomes an audit item) or keep our own objects.
6. **GRH framing.** Beyond Dirichlet (where the positivity route would be new) or an independent route for Dirichlet.
7. **WHKs vs WKH.** The paper uses WHK as the owner asked; the DMP texts are unchanged.
8. **GU's checkable consequence.** *Answered 2026-11-24:* uniform charge quantisation, with the unit guaranteed by the ODP (IX.5f).
10. **Non-triviality and DMP-completeness.** *Answered 2026-11-24:* the scale-uniform lower edge is part of the one assumption
   (X.64a), conditional on it and placed at the ODP's end (III.9.5b); DMP-complete means runs on DMP (X.64b); Navier-Stokes is not
   DMP-complete, with blowup as the expected, falsifiable consequence (VI.7e).
9. **The personal note.** It still says "One thing led to three"; the paper now covers seven problems.
