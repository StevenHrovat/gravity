# The three-problem paper: outline (draft 1, 2026-11-23)

**Working title.** *Positivity, contraction and the existence boundary: one chain behind Yang-Mills, GRH and P vs NP.*

**Goal (the owner's words).** "This should be immaculate in both its magical logical simplicity through ultimate reduction, while
being informative enough to all the different fields that need its tools by being intuitively understandable and guiding the reader
through the easiest to understand part, DMP, then extending it with tools that just click."

**State.** None of the three problems is solved by this work. Each has a large proved core, much of it in Lean, and named open steps.
The paper is built so that each open step, when it closes, changes one row of `CLAIMS.md`, one verdict line in its part and one
item of the abstract, and nothing else.

## Files

| File | What | State |
|---|---|---|
| `OUTLINE.md` | this file: structure, one paragraph per section, status per section | draft 1 |
| `CLAIMS.md` | every claim of the draft: status, source, what would upgrade it (165 rows) | draft 1 |
| `draft/00-abstract-introduction.md` | abstract and introduction | drafted |
| `draft/01-part-I-dmp.md` | Part I, DMP | fully drafted |
| `draft/02-part-II-tools.md` | Part II, the tools | fully drafted |
| `draft/03-part-III-yang-mills.md` | Part III | dense skeleton |
| `draft/04-part-IV-grh.md` | Part IV | dense skeleton |
| `draft/05-part-V-pnp.md` | Part V | dense skeleton |
| `draft/06-part-VI-common-step.md` | Part VI | drafted (short) |

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

## Part III. Yang-Mills: everything reduces to one box at one scale

* **III.0 What is proved and what is not.** Minting half done in Lean (conditional on stated inputs); gap mechanism reduced to one
  box. Open: O1 the one-box statement; O2 line of constant physics and non-triviality; O3 continuum field theory (Euclidean
  invariance, fields, uniqueness, reconstruction; external for the external construction, open for ours); O4 other groups.
  "One box at one scale" is exact for the gap mechanism, not for the Clay statement.
* **III.1 Lattice theory and positivity.** Wilson measure, RP, transfer kernel, 't Hooft duality, good blocking, Z_tw < Z. *Lean
  (one paper item).*
* **III.2 Minting half.** Dobrushin with weights, Corollary B, windowed OS route, top-level assembly, both orders of limits,
  non-triviality of hypotheses. *Lean; MassGapLoc -> continuum spectral gap paper.*
* **III.3 Pressing half: reduction to one box.** Hand-over 0.881, forced sheet, superadditivity, uniformity, doubling law,
  saturation, uncontained sheets; **III.3.8 the one-box statement: open.** Care point: which Lean input form is exactly III.3.8.
* **III.4 The one box from inside.** Dichotomy (a) fails at the SO(3) cut (paper); reduction to two bad events (paper); window
  0.18-1.79 nats (Lean + paper); Y2-Y5 open; coarse test (numerical); IR column (open, knife-edge certificate as named hypothesis).
* **III.5 Weak-coupling side and continuum.** UV stability and the continuum limit (external); Balaban reading (classical); M1
  (paper); O2-O4.
* **III.6 Readings.** WHKs, pressing/minting, CMOS collapse, spanned existence. *reading.*
* **III.7 What would close it.** O1 first (the mathematical core), then O2-O4.

## Part IV. GRH: the positivity route

* **IV.0 State.** RH and Dirichlet GRH proved in Lean by others, not via positivity (external); GRH beyond Dirichlet open; this part
  proves no case of GRH and gives an independent reduction.
* **IV.1 Finite models.** Weil criterion, similitude, skew shift, Krein counterexample (duality without positivity fails), Lee-Yang
  small cases, periodic points. *Lean.*
* **IV.2 The bridge.** Pringsheim-Landau, negative-residue poles (Lean); the real-zero computation (classical); function-field
  duality (classical); arithmetic Hodge index (open).
* **IV.3 Measured shape of the missing positivity.** Semilocal test, prime-by-prime induction, exact cancellation at every step,
  weight positivity insufficient. *numerical + classical.*
* **IV.4 The open step in five forms.** Weil Hilbert space, critical ferromagnet, Deninger space, local reflection rule,
  Hermite-Biehler coupling. *open; 2 and 3 imply 1 (paper).*
* **IV.5 Readings. IV.6 What would close it.**

## Part V. P vs NP: inside a certified class, and across it

* **V.0 State.** Neither P vs NP nor NP vs coNP is resolved.
* **V.1 Inside the class.** Dobrushin sampling, spectral gap, Doeblin (Lean); uniqueness, JVV, Weitz, LLL class (classical).
* **V.2 At the edge.** Antiferromagnetic and k-CNF hardness (conditional on NP != RP); ferromagnets stay easy (classical).
* **V.3 Refutations.** Soundness and completeness, cut principle, size-width, Tseitin, Gauss law, every refutation crosses (Lean);
  known lower bounds and interpolation (classical / conditional); Frege open.
* **V.4 Native method and the floor.** *Lean + numerical; reading for the floor.*
* **V.5 Open steps N1-N4 and the three barriers.**
* **V.6 Readings.**

## Part VI. The common open step

One shape: positivity or a certificate known for one unit, missing for every case. What the act-carrier answer settled (Yang-Mills
reduced to one box) and did not (GRH, P vs NP). What would close each. Why Yang-Mills is the model: the only problem whose starting
positivity is given by construction. How the paper closes locally.

---

## Where the draft most needs the owner's input

1. **The one-box statement in its final form.** Which of the Lean input forms is exactly the statement the paper calls O1, and the
   owner's worst-case argument for one DB, stated so it can be checked.
2. **How much of DMP to quote, and in whose voice.** Part I quotes the author's words sparingly and marks every reading. The owner
   decides the balance between the protocol's own text (trust, witnesses, minting) and the physical readings (existence, DB, ODP).
3. **The title and the claim scope of the abstract.** The draft's title avoids claiming a solution; the abstract lists what is not
   proved. The owner decides whether the paper is framed as "one chain behind three problems" (as now) or as an attempt.
4. **O2-O4 for Yang-Mills.** Whether the paper adopts the external continuum construction's field notion (then O3 becomes an audit
   item) or keeps its own objects (then rotation invariance must be addressed).
5. **GRH framing after the Lean proof by others.** Whether Part IV aims at GRH beyond Dirichlet L-functions (where the positivity
   route would be new) or presents itself as an independent route for Dirichlet L-functions.
6. **WHKs vs WKH.** The DMP texts say White Key Holders (WKH); the owner prefers White Hole Keys (WHK). The paper uses WHK as the
   owner asked; the DMP texts are unchanged.
