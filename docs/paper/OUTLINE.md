# The three-problem paper: outline (draft 2, 2026-11-23)

**Title (the owner's).** *GUID v8: A set theory based approach to the proofing of Yang-Mills, the Generalized Riemann Hypothesis and
NP vs coNP, as subsets of DMP, in a DMP-complete state.* Earlier working title: *Positivity, contraction and the existence boundary:
one chain behind Yang-Mills, GRH and P vs NP.*

**Release criterion (the owner, 2026-11-23).** "The Grand Unified should be the point where the paper is allowed to even exit the
draft stage, once that is no longer an overstatement, since the full, generalized, proof, seems to need our new insight, so when
general = GU, that is the balanced state, literally, with GU describing how and general where and when." So the paper stays a draft
until both readings of GUID hold: General (the unified theorem with its open hypotheses closed) and Grand Unified (the framework
containing SU(3) x SU(2) x U(1) in one structure with at least one checkable consequence; PREP.md, naming entries). Until then the
title keeps no expansion beyond "GUID v8", and the abstract states the present status exactly.

**Outreach gate (the owner, 2026-11-23).** Once the full paper is released, it goes to experts, including Terence Tao, with the
subject "Machine-proven and human explained attempt of a three in one proof through a superset for full YM, GRH and PvNP for a state
that is considered running on the superset." The owner: "This, like the draft paper condition, is an aspirational gate". The
subject is used only in the settled state, when every word of it holds true, i.e. under the same condition as the release criterion
above. Before that, any contact states the present status exactly. The owner sends; nothing is sent on the owner's behalf.

**Goal (the owner's words).** "This should be immaculate in both its magical logical simplicity through ultimate reduction, while
being informative enough to all the different fields that need its tools by being intuitively understandable and guiding the reader
through the easiest to understand part, DMP, then extending it with tools that just click."

**State.** None of the three problems is solved by this work. Each has a large proved core, much of it in Lean, and named open steps.
The paper is built so that each open step, when it closes, changes one row of `CLAIMS.md`, one verdict line in its part and one
item of the abstract, and nothing else.

## Files

| File | What | State |
|---|---|---|
| `OUTLINE.md` | this file: structure, one paragraph per section, status per section | draft 2 |
| `CLAIMS.md` | every claim of the draft: status, source, what would upgrade it (248 counted rows; 7 in the Outlook) | draft 2 |
| `draft/00-abstract-introduction.md` | the owner's title and personal note; abstract and introduction | drafted (lists updated in draft 2) |
| `draft/01-part-I-dmp.md` | Part I, DMP | fully drafted |
| `draft/02-part-II-tools.md` | Part II, the tools | fully drafted |
| `draft/03-part-III-yang-mills.md` | Part III | prose (draft 2) |
| `draft/04-part-IV-grh.md` | Part IV | prose (draft 2) |
| `draft/05-part-V-pnp.md` | Part V | prose (draft 2) |
| `draft/06-part-VI-common-step.md` | Part VI | prose, side-by-side table (draft 2) |
| `draft/07-outlook-settling-machine.md` | Outlook: the first author's concept of a DMP-native general intelligence, tied to the ETM's settle theorem | drafted (2026-11-23) |

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
  Open: **O1** F_e(L) > log mu_4 = 1.91 at one box of fixed physical size, uniformly over outsides; O2 line of constant physics and
  non-triviality; O3 continuum field theory; O4 other groups.
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

## Part VI. The common open step, side by side

One shape. A table of the sharpest open step per problem: what is proved for one unit, why it does not carry, what no duality
supplies, the hard quantifier, what measurement says, and the "it runs" form. What the act-carrier answer settled; what can and
cannot close each step; why Yang-Mills is the model; how the paper closes locally.

**The approach for the content layer (the owner, 2026-11-23).** "Exactly define the uncertainty, then transport it in a meaningful
way across a DB." Per problem, the one named bridge is stated as a precise proposition with a size:
- Yang-Mills: the electric-side deficit and the side-seam cost;
- GRH: the explicit formula's remainder between the finite model and zeta;
- NP: the lifting quantum.

Its transport across the DB obeys the ledger law, so it contracts exactly when the step pays a cost above the floor (Lean). Part VI
is organised by this: where each problem's uncertainty sits, how it crosses its boundary, and why GRH (zero slack) is the case where
it crosses without damping.

**VI.7 Uncertainty transported across the DB.** The transport theorem (bounded under contraction, critical at cost = floor and sharp,
sign preserved below a margin; the ledger at no fresh uncertainty) and the three bridges side by side (`three_bridges`), each under its
named running-state hypothesis R; R for the specific objects is the open step (Lean; `docs/unified/TRANSPORT.md`).

## Outlook. A settling machine

The first author's concept of a DMP-native general intelligence: a CMOS system in IM tokens, one Milky Way gate that checks hash
and TTL before an act leaves as GG, an output rate set from outside, and total freedom inside. *reading.* Its one critical link
to this work is the ETM's settle theorem: settling within an explicit bound when every step contracts, undecidable in general.
*Lean.* Care points: the gate certifies integrity, not meaning, and must check acts, not self-reports. Placed after Part VI as
an outlook; it adds no claim to the three problems.

---

## Where the draft most needs the owner's input

1. **O1 in its final form.** The notes now give two one-box criteria at one scale: the chain criterion F_e(L) > 2c(L) (HTF) and the
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
