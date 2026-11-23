# Proof systems: NP vs coNP, and the flux loss of the assertion of existence

Private working note, 2026-11-23. It takes up the owner's two readings of the same day (entries in
`../mass-gap/weak-coupling/PREP.md`, "P vs NP, the approach reversed"):

> "we should show that the definition of existence at G0 can be extended to wherever we need it to be for everything
> to be describable in it, which is done through the universal language IM"

> "The lower bound to the NP = coNP is the flux loss of the assertion of existence that is associated with it."

The note frames the question (Cook-Reckhow), lists what is known and what is open, tests the "flux loss" reading
against the known lower-bound mechanisms, proves the parts that are solid in Lean, and stops at the first step that
cannot be closed. It continues `DICTIONARY.md` (sampling and counting) on the side of proofs.

**Claim marks** (as in the dictionary)

| Mark | Meaning |
|---|---|
| **[Lean]** | Proved in this repository, `docs/mass-gap/formal/ProofPhase/Proof/` (Lean 4.34.0, Mathlib v4.34.0, standard axioms only; `axioms-proof.sh`, `axioms-proof.log`: 69 declarations, no `sorry`). Hypotheses listed with each theorem. |
| **[classical]** | A published theorem; reference in section 9. Not re-proved here. |
| **[conditional]** | A published theorem that holds under a stated assumption (here cryptographic). |
| **[reading]** | An interpretation: a way of putting two results side by side. Not a theorem. |
| **[open]** | Not settled. |

---

## 0. The short answer

1. **The owner's reversal lands on the Cook-Reckhow programme.** A universal language in which every non-existence
   (every unsatisfiable formula) has a certificate exists: resolution is complete. Whether every such certificate can
   be short is exactly NP = coNP (Cook-Reckhow 1979). NP != coNP would imply P != NP. **[classical]**
2. **Lower bounds are known system by system, and stop below Frege.** Exponential lower bounds are known for
   resolution, cutting planes, polynomial calculus and bounded-depth Frege. None is known for Frege or extended Frege,
   and for those systems the main lower-bound tool (feasible interpolation) provably fails under standard
   cryptographic assumptions. **[classical]**, **[conditional]**, **[open]**
3. **"Flux loss" is a real lower-bound mechanism.** In resolution it is exactly two of the known ones, and both are
   proved here. **[Lean]**
   * **Bottleneck counting.** The falsifying assignments flow from the root of a refutation (where all of them are
     alive) down to the axioms (where each is killed). One resolution step can lose flux but never create it. So a
     tree-like refutation has at least |T|/k leaves when each axiom absorbs at most k of the assignments in T.
   * **The cut principle.** Measure a clause by how many constraints it asserts. The measure starts at 1 on the
     axioms and must reach the whole system at the root, and one step can lose assertion but never create it. So some
     clause asserts a middle-sized region. That clause must name every variable on the boundary of its region, which
     makes its width at least the boundary. For Tseitin formulas the flux is literally a conserved parity flow
     (Kirchhoff's law mod 2), and the bound is width at least the edge expansion.
   * **Width becomes size.** Tree-like size is more than 2^(width - axiom width) (Ben-Sasson-Wigderson, tree-like
     case).
4. **The candidate principle, stated.** A lower bound follows from three things:
   * (i) a measure of what a line asserts, created by no inference step;
   * (ii) a crossing cost: every line that asserts a middle-sized region pays at least b;
   * (iii) a conversion from crossing cost to proof size.

   Resolution passes all three (section 6). For Frege, (i) holds automatically, but (ii) and (iii) fail as stated: a
   Frege line can name a conserved binary flux (a parity) at polynomial cost. Tseitin formulas, hard for resolution,
   have short Frege proofs for exactly this reason. **[reading]** on **[classical]**
5. **The first step that cannot be closed.** For Frege, an explicit family of formulas where every refutation must
   contain a line whose crossing cost is superpolynomial. This needs two things, both open:
   * a superpolynomial formula-size lower bound for an explicit function (the best known are about n^3);
   * a transfer from "this line asserts the boundary" to "this line computes the hard function". Interpolation is
     such a transfer, and it fails for Frege under cryptographic assumptions.

   **[open]** In Lean, the first known step not formalized here is the DAG-like size-width relation (section 4).

---

## 1. From the owner's reversal to Cook-Reckhow

**Proof systems.** A propositional proof system is a polynomial-time checker V(F, pi) such that:
* the formula F is unsatisfiable exactly when some pi makes V accept (sound and complete);
* pi is then a refutation of F: a certificate of non-existence.

The system is **polynomially bounded** if every unsatisfiable F has a refutation of size polynomial in |F|.

**Cook-Reckhow (1979).** A polynomially bounded proof system exists if and only if NP = coNP. **[classical]**
* One direction: such a system puts UNSAT, which is coNP-complete, into NP (guess the short refutation, check it).
* The other: if UNSAT is in NP, its NP verifier is a polynomially bounded proof system.

NP != coNP implies P != NP, since P is closed under complement.

**The owner's reversal, read in these terms.** **[reading]**

| The owner's words | Standard counterpart |
|---|---|
| "the definition of existence at G0 can be extended to wherever we need it to be" | Extend the certificates from existence (a satisfying assignment, the NP side) to non-existence (a refutation, the coNP side). The earlier entry "existence has to also describe what does not exist" asks for exactly this. |
| "for everything to be describable in it" | **Completeness.** Every unsatisfiable formula has a refutation; for resolution, one of at most 2^n leaves always exists (split on every variable). So the extension exists. **[classical]** |
| "through the universal language IM" | A universal proof language. Two classical facts make "universal" precise. Cook-Levin: every NP question is a SAT question. An optimal proof system (one whose refutations are at most polynomially longer than any other system's) exists if NE = coNE (Krajicek-Pudlak 1989). **[classical]**; whether one exists is **[open]** |
| (the question left) | Not whether non-existence can be described, but **how long** its description must be. That is NP vs coNP. |

So the reversal changes the target from P vs NP to NP vs coNP (a stronger separation). It moves the work from
algorithms to proofs. Its cost is that the question becomes one about the length of descriptions, and the owner's
second entry (flux loss) is a proposal for measuring that length.

## 2. What is known, and where it stops

**Cook's programme:** prove superpolynomial lower bounds for stronger and stronger proof systems. Each system below
simulates the one above it.

| System | A line is | Lower bound | Mechanism | Status |
|---|---|---|---|---|
| Tree-like resolution | a clause | exp, many families | Prover-Delayer games; size-width (tree-like) | **[classical]**, size-width **[Lean]** |
| Resolution | a clause | exp: pigeonhole (Haken 1985), Tseitin on expanders (Urquhart 1987), random 3-CNF (Chvatal-Szemeredi 1988) | bottleneck counting (Haken); width via expansion and size-width (Ben-Sasson-Wigderson 2001) | **[classical]**, the width side **[Lean]** |
| Polynomial calculus | a polynomial | degree lower bounds (Razborov 1998; Impagliazzo-Pudlak-Sgall 1999) | degree, the algebraic width | **[classical]** |
| Cutting planes | a linear inequality | exp: clique-coloring (Pudlak 1997); random CNFs (Fleming-Pankratov-Pitassi-Robere 2017; Hrubes-Pudlak 2017) | feasible interpolation: a refutation yields a small (monotone real) circuit separating two sides | **[classical]** |
| Bounded-depth Frege | a formula of depth d | exp for pigeonhole (Ajtai 1988; Krajicek-Pudlak-Woods 1995; Pitassi-Beame-Impagliazzo 1993) | switching lemma (the AC^0 circuit lower-bound tool) | **[classical]** |
| AC^0[p]-Frege | depth d with mod-p gates | none superpolynomial, although AC^0[p] circuit lower bounds are known (Razborov 1987, Smolensky 1987) | | **[open]** |
| Frege | any formula | none superpolynomial | | **[open]** |
| Extended Frege | any circuit (by abbreviation) | none superpolynomial | | **[open]** |

**Barriers that apply to proof-complexity lower bounds.**

* **Interpolation fails above cutting planes (cryptographic barrier).** Feasible interpolation turns a short
  refutation of A(x, y) and B(x, z) (A and B share only x) into a small circuit computing an interpolant. For extended
  Frege it fails unless RSA is insecure (Krajicek-Pudlak 1998). For Frege and TC^0-Frege it fails unless factoring
  Blum integers is easy (Bonet-Pitassi-Raz 2000). For bounded-depth Frege of some fixed depth it fails under
  Diffie-Hellman (Bonet-Domingo-Gavalda-Maciel-Pitassi 2004). So the tool that works for cutting planes cannot be the
  tool for Frege. **[conditional]**
* **Natural proofs in proof form.** Razborov (1995) showed that if strong pseudorandom generators exist, then certain
  fragments of bounded arithmetic cannot prove superpolynomial circuit lower bounds. A related research line studies
  "proof complexity generators" (Krajicek; Alekhnovich-Ben-Sasson-Razborov-Wigderson), pseudorandom-generator
  tautologies conjectured hard for strong systems. The lesson matches Razborov-Rudich: a lower-bound method that is
  itself efficient and broadly applicable would break cryptography. **[conditional]**
* **Lower bounds track circuit lower bounds.** Each system's lower bound has used a lower-bound technique for the
  circuit class its lines live in:
  * switching for AC^0 lines;
  * monotone circuit bounds for cutting planes via interpolation.

  Frege lines are formulas (NC^1) and extended Frege lines are circuits (P/poly). Superpolynomial lower bounds for
  explicit functions are open in both classes; the best formula lower bounds are about n^3 (Hastad 1998, Tal 2014).
  **[classical]** (pattern), **[reading]** (that it continues).
* **Relativization, for the last step.** There are oracles A with NP^A = coNP^A and B with NP^B != coNP^B
  (Baker-Gill-Solovay 1975). So the final step, from "every specific system needs long proofs" to "NP != coNP",
  cannot relativize. Lower bounds for one fixed system are not hit by this barrier, but they never add up to the
  whole: there is always a stronger system, unless an optimal one exists. **[classical]**

## 3. Lean part 1: resolution and the flux of falsifying assignments

File `ProofPhase/Proof/Resolution.lean`. **[Lean]**, no hypotheses beyond the definitions.

**Definitions.**
* A literal is a variable with a sign, a clause a finite set of literals, a CNF a finite set of clauses.
* The resolution rule derives (P \ {y}) union (Q \ {not y}) from a clause P containing y and a clause Q containing
  not y.
* `TL F C s`: C has a tree-like derivation from F with s leaves.

| Result | Statement |
|---|---|
| `falsifies_res` | An assignment falsifying the resolvent falsifies one of the two premises. |
| `TL.exists_falsified`, `TL.unsat` | **The path of one assignment.** Follow the falsified premise from the root: it ends at an axiom the assignment falsifies. This is the search reading of a refutation, and it is soundness. |
| `flux_empty` | At the root all of T is alive: the flux through the empty clause is \|T\|. |
| `flux_res` | **No flux is created by a step:** flux(resolvent) <= flux(P) + flux(Q). The slack is the loss. |
| `TL.flux_le`, `TL.card_le` | **Leaf bottleneck counting.** If each axiom absorbs at most k assignments of T, every tree-like refutation has at least \|T\| / k leaves. |
| `fullCNF_leaves` | Worked case: the complete CNF on n variables (all 2^n full clauses) needs at least 2^n leaves. Each axiom absorbs exactly one assignment. The input has 2^n clauses itself, so this shows the mechanism, not a superpolynomial bound. |
| `TL.restrict` | **Restriction:** setting a literal true turns a derivation of C into one of a subclause of the restricted C from the restricted CNF, with no more leaves. |

**What is new:** the whole calculus; Mathlib has no resolution. **What the flux bound misses for DAG-like proofs:**
a line can be reused, so the flux through it is counted once but used many times. Haken's DAG argument therefore
needs a cut of "fat" lines that every assignment's path must cross, not the leaves. **[classical]**, not formalized.

## 4. Lean part 2: width becomes size (tree-like)

File `ProofPhase/Proof/SizeWidth.lean`. **[Lean]**

`WD F W C`: C has a resolution derivation from F (lines may be reused) in which every clause, axioms included, has at
most W literals.

| Result | Statement |
|---|---|
| `tl_width` | Axioms of at most w literals and a tree-like refutation with at most 2^d leaves give a refutation of width at most w + d. |
| `tl_size_gt` | **Read backwards:** if F has no refutation of width W >= w, every tree-like refutation has more than 2^(W - w) leaves. |
| `WD.lift`, `WD.trans`, `WD.combine` | The three steps of the proof: lift a restricted refutation by one literal, replace axioms by derivations, glue the two halves. |

**The proof, in words.** The last step of a refutation resolves {y} against {not y}. Restricting by y := false and
y := true gives refutations of the two halves, and one of them has at most half the leaves. By induction on the number
of literals:
* the small half gets width w + d - 1, and the large half w + d;
* lifting the small half back costs one literal and derives {y};
* resolving {y} against the axioms that contain not y rebuilds the large half's axioms within width w + d.

**In flux language:** a crossing of the cut at y costs one literal of width, paid by the side that is cheap in
size. **[reading]**

**Not formalized here:** the DAG-like relation, size at least exp((W - w)^2 / (8n)) for n variables (Ben-Sasson-Wigderson
2001). Its extra step is a random restriction that kills every wide clause, plus a count of how many survive.
**[classical]**. This is the first known step not formalized: no obstacle in principle, it was out of this session's
scope.

## 5. Lean part 3: the cut principle, and Tseitin's conserved flux

Files `ProofPhase/Proof/Cut.lean` and `ProofPhase/Proof/Tseitin.lean`. **[Lean]** with two stated hypotheses about the
input, none about proofs.

**Setting.** The CNF is a union of blocks, one per node v of a finite set V. `Implies S C`: the blocks in S together
force the clause C. The measure `mu C` (Ben-Sasson-Wigderson) is the least number of blocks that force C: **the size
of the region whose existence the clause asserts.**

| Result | Statement |
|---|---|
| `mu_ax` | An axiom asserts at most one block. |
| `mu_res` | **Assertion is not created:** mu(resolvent) <= mu(P) + mu(Q). |
| `mu_empty` | If every proper sub-system is satisfiable, the empty clause asserts all \|V\| blocks. |
| `exists_middle` | So every refutation contains a clause asserting more than K/2 and at most K blocks, for any 1 <= K < \|V\|. |
| `mem_of_boundary` | **The boundary lemma.** Let S be a smallest region forcing C, u in S, and x a variable that toggles the block at u and is invisible to the other blocks of S. Then x occurs in C. Without x, C cannot tell the region with u from the region without it. |
| `width_ge` | **Cut principle.** If every middle-sized region has at least e boundary variables, every refutation has width at least e. |
| `tl_size_ge` | And then every tree-like refutation has more than 2^(e - 1 - w) leaves. |

**Tseitin formulas.** Vertices V, edges as variables, a charge c(v) at each vertex. The constraint at v says that the
number of true edges at v has parity c(v). The edge values are a flow mod 2 with divergence c: Kirchhoff's law mod 2,
the Gauss law of a Z_2 gauge field. With odd total charge the formula is unsatisfiable, because every edge is counted
at both ends.

| Result | Statement |
|---|---|
| `satB_block_iff` | The CNF block at v (one clause per wrong-parity pattern) holds exactly when the parity at v is c(v). |
| `toggle`, `invisible` | Flipping an edge at u toggles u's constraint; flipping an edge not at v leaves v unchanged. These are the two properties the boundary lemma asks for. |
| `Tseitin.width_ge` | **Width at least the edge expansion:** if every vertex set S of middle size has at least e edges at exactly one of its vertices, every resolution refutation has width at least e. |
| `Tseitin.tl_size_ge` | Tree-like size more than 2^(e - 1 - w), w the largest degree. |

**Hypotheses, stated (both about the graph):**
* every proper sub-system is satisfiable. Classical for a connected graph: flip a path from a violated vertex to a
  vertex outside S. Not formalized.
* the expansion count. For an explicit bounded-degree expander family, e is linear in |V|: a theorem of graph theory,
  not formalized.

With both, the Lean result is the exponential tree-like lower bound for Tseitin formulas on expanders. With the DAG
size-width relation (section 4, classical) it becomes Urquhart's exponential resolution lower bound. **[classical]**

## 6. Testing the owner's "flux loss" against the known mechanisms

**The question asked:** is "the flux loss of the assertion of existence" one of the known lower-bound mechanisms, an
information or width cost across a cut?

**Answer: yes, in resolution it is two of them exactly.** **[reading]** on **[Lean]**

| The owner's words | Bottleneck counting (section 3) | Cut principle (section 5) |
|---|---|---|
| assertion of existence | for each candidate existence (assignment), the line where it is killed | what a clause asserts: the region mu(C) of constraints it carries |
| flux | the falsifying assignments, flowing from the root (all alive) to the axioms (each killed) | the assertion measure, flowing from the axioms (1 each) to the root (the whole system) |
| loss | the slack in flux(resolvent) <= flux(P) + flux(Q): each step resolves a variable away, and that information is dropped | the slack in mu(resolvent) <= mu(P) + mu(Q): assertion can be lost, never created |
| lower bound | a line absorbs at most k, so at least \|T\|/k lines | crossing the middle band costs one literal per boundary variable, so width is at least the boundary, and size at least 2^(width) |

The other known mechanisms fit the same frame:
* **Interpolation** (cutting planes) is the "transport across a cut" form. The proof must carry information about the
  shared variables x from the y side to the z side, and the interpolant circuit is the record of what crossed.
* **Degree** (polynomial calculus) is width in algebraic dress.
* **The switching lemma** (bounded-depth Frege) is the conversion step: a random restriction collapses every line to
  a shallow decision tree, so no line can carry much.

**The candidate principle (flux-loss lower bound).** For a proof system P and a family of unsatisfiable formulas,
suppose:
1. **No creation.** A measure m on lines with m(axiom) <= 1, m(conclusion) <= the sum of m over the premises, and
   m(contradiction) = N. *For any sound system with a bounded number of premises per rule, the semantic measure mu of
   section 5 has this property; the proof of `mu_res` uses only soundness.*
2. **Crossing cost.** Every line with N/3 < m <= 2N/3 has cost at least b, in the system's own size measure.
3. **Conversion.** Cost b on one line forces total proof size at least f(b).

Then every P-refutation has size at least f(b). **[reading]**; the assembly is trivial, all the content is in 2 and 3.

**Checked against resolution.** 1 is `mu_res`. 2 is `Tseitin.width_ge`, with cost = width and b = expansion. 3 is
`tl_size_gt` for tree-like proofs, and the DAG size-width relation (classical) for general ones. **All three hold, and
the principle reproduces Urquhart's theorem.** **[Lean]** for tree-like, **[classical]** for DAG.

**What it would need for Frege.**
* **Step 1 holds automatically.**
* **Step 2 fails for Tseitin formulas, and the reason is instructive.** A Frege line asserting a middle region of a
  Tseitin formula can say "the parity of the boundary edges is c(S)" with a formula of size polynomial in b (parity
  has quadratic-size formulas). Tseitin formulas do have polynomial-size Frege proofs (Urquhart 1987). Resolution
  cannot name the parity: a clause has to list one of 2^(b-1) patterns, so it pays b literals. **The crossing cost is
  the cost of naming the conserved quantity**, and Frege names a binary flux cheaply. **[classical]** (the facts),
  **[reading]** (the moral).
* **So step 2 for Frege needs a conserved quantity that no small formula can name.** That is a superpolynomial
  formula-size lower bound for an explicit function, an open problem in circuit complexity (best known: about n^3).
* **Step 3 for Frege needs a transfer** from "some line asserts the boundary" to "some line computes the hard
  function". Interpolation is the known transfer, and it fails for Frege under cryptographic assumptions (section 2).
* **For extended Frege**, lines are circuits, so step 2 needs a circuit lower bound outside P/poly. There the natural
  proofs barrier applies to the measure itself, unless the cost is specific to one hard function.

**Verdict.**
* The owner's principle is correct as a lower-bound mechanism and is the right shape: a conserved assertion, lost and
  never created, that must cross a middle boundary at a cost.
* It proves what is known up to bounded-depth Frege.
* For Frege and beyond, its crossing-cost step is equivalent in difficulty to explicit formula or circuit lower
  bounds, and its conversion step meets the interpolation barrier.

It does not get past them by itself. **[reading]**

## 7. DMP reading (separate, marked)

This section states the owner's DMP entries in the language of sections 1 to 6. Everything here is **[reading]**
unless marked otherwise.

* **G0 extended through IM.** Extending the definition of existence to cover non-existence is extending certificates
  from NP to coNP.
  * Completeness, "everything describable", holds and is classical.
  * The content is the **cost** of the description. The earlier entry "existence = non-existence + 1" matches it
    exactly: the description of a non-existence (a refutation) is an object of its own, and its size is the question.
* **"Only existence crosses a boundary, information is radiated as loss"** (PREP, cycle 5). In resolution each step
  strips one variable, the resolved one: information radiated as loss. What reaches the root is the bare assertion
  "nothing exists" (the empty clause). The flux and assertion measures are conserved with loss along the proof,
  `flux_res` and `mu_res` **[Lean]**.
* **Tseitin is the binary flux sector.** The Tseitin constraint is the Gauss law of a Z_2 gauge field: the same
  structure as the centre (binary) flux of the Yang-Mills entries, the one datum that crosses a blocking boundary
  intact. The width lower bound says that to refute "odd total charge", a resolution proof must at some point carry
  the flux through the boundary of a middle region. Since a clause cannot name the flux, it pays one literal per
  boundary edge: **width is at least the area of the boundary**, an area law for proofs. On a d-dimensional grid of
  side L that boundary is of order L^(d-1). That is isoperimetry, **[classical]**, not formalized.
* **Why stronger systems escape: naming the binary datum.** The owner's earlier reading says only the binary
  existence datum crosses. A proof system that can name that datum directly (Frege names a parity in one short line)
  carries it across for free, and the flux-loss bound disappears. That is exactly why Tseitin formulas are hard for
  resolution and easy for Frege. So the DMP prediction is:
  * flux-loss lower bounds hold for proof languages that **cannot name the conserved flux**;
  * against a language that can name every efficiently computable quantity (extended Frege), a lower bound would need
    a conserved flux that **no efficient description names**. That is the shape of a pseudorandom object, and it is
    where the cryptographic barriers of section 2 sit.

  Read through DMP, NP != coNP becomes: there is an existence whose non-existence cannot be described cheaply in any
  universal language, because its conserved flux has no short name. That restates the open problem; it does not solve
  it.
* **What DMP adds, and what it does not.** It gives the right invariant shape: conserved assertion, loss, boundary
  cost. Section 6 shows this shape reproduces the known lower bounds. It does not supply the missing ingredient for
  Frege: an explicit conserved quantity with no short formula. That is a circuit lower bound, and DMP names no
  candidate function.

## 8. What is proved, what is conditional, what is missing

**Proved [Lean]** (69 declarations, standard axioms only):
* resolution: soundness and the search path;
* the flux of falsifying assignments, created by no step;
* leaf bottleneck counting, with the complete CNF as a worked case;
* restriction;
* the tree-like size-width relation (Ben-Sasson-Wigderson);
* the cut principle: the measure is created by no step, a middle clause exists, the boundary lemma, width at least
  the boundary count;
* Tseitin: the CNF block is the parity constraint, toggling, invisibility, width at least the edge expansion,
  tree-like size at least 2^(e - 1 - w).

**Hypotheses carried:** for Tseitin, satisfiability of proper sub-systems (classical for connected graphs) and the
expansion count (classical for explicit expanders).

**Classical, not formalized:**
* the DAG-like size-width relation;
* Haken's DAG bottleneck counting (pigeonhole);
* Urquhart's and Chvatal-Szemeredi's resolution bounds;
* cutting planes via interpolation;
* bounded-depth Frege via switching;
* Cook-Reckhow.

**Conditional:** no feasible interpolation for extended Frege, Frege, TC^0-Frege and bounded-depth Frege of some
depth, each under a cryptographic assumption.

**Missing, in order:**
1. **Lean, known mathematics:**
   * the DAG-like size-width relation;
   * satisfiability of proper Tseitin sub-systems on connected graphs (path flipping);
   * an explicit expander family.

   With these, Urquhart's exponential resolution lower bound would be fully formal.
2. **The first step that cannot be closed (open mathematics).** Step 2 of the flux-loss principle for Frege: an
   explicit family where every refutation has a line of superpolynomial crossing cost. It needs a superpolynomial
   formula lower bound for an explicit function, plus a transfer that survives the interpolation barrier.
3. **Beyond:**
   * extended Frege (circuit lower bounds, where natural proofs applies);
   * the step from "every specific system" to NP != coNP (no optimal system is known; the step cannot relativize).

## 9. References

* M. Ajtai, The complexity of the pigeonhole principle, FOCS 1988.
* M. Alekhnovich, E. Ben-Sasson, A. Razborov, A. Wigderson, Pseudorandom generators in propositional proof
  complexity, SIAM J. Comput. 34 (2004).
* T. Baker, J. Gill, R. Solovay, Relativizations of the P =? NP question, SIAM J. Comput. 4 (1975).
* E. Ben-Sasson, A. Wigderson, Short proofs are narrow: resolution made simple, J. ACM 48 (2001).
* M. L. Bonet, T. Pitassi, R. Raz, On interpolation and automatization for Frege systems, SIAM J. Comput. 29 (2000).
* M. L. Bonet, C. Domingo, R. Gavalda, A. Maciel, T. Pitassi, Non-automatizability of bounded-depth Frege proofs,
  Comput. Complexity 13 (2004).
* V. Chvatal, E. Szemeredi, Many hard examples for resolution, J. ACM 35 (1988).
* S. Cook, R. Reckhow, The relative efficiency of propositional proof systems, J. Symbolic Logic 44 (1979).
* N. Fleming, D. Pankratov, T. Pitassi, R. Robere, Random Theta(log n)-CNFs are hard for cutting planes, FOCS 2017.
* A. Haken, The intractability of resolution, Theoret. Comput. Sci. 39 (1985).
* J. Hastad, The shrinkage exponent of de Morgan formulas is 2, SIAM J. Comput. 27 (1998).
* P. Hrubes, P. Pudlak, Random formulas, monotone circuits, and interpolation, FOCS 2017.
* R. Impagliazzo, P. Pudlak, J. Sgall, Lower bounds for the polynomial calculus and the Groebner basis algorithm,
  Comput. Complexity 8 (1999).
* J. Krajicek, Interpolation theorems, lower bounds for proof systems, and independence results for bounded
  arithmetic, J. Symbolic Logic 62 (1997).
* J. Krajicek, P. Pudlak, Propositional proof systems, the consistency of first order theories and the complexity of
  computations, J. Symbolic Logic 54 (1989).
* J. Krajicek, P. Pudlak, Some consequences of cryptographical conjectures for S^1_2 and EF, Inform. and Comput. 140
  (1998).
* J. Krajicek, P. Pudlak, A. Woods, An exponential lower bound to the size of bounded depth Frege proofs of the
  pigeonhole principle, Random Structures Algorithms 7 (1995).
* T. Pitassi, P. Beame, R. Impagliazzo, Exponential lower bounds for the pigeonhole principle, Comput. Complexity 3
  (1993).
* P. Pudlak, Lower bounds for resolution and cutting plane proofs and monotone computations, J. Symbolic Logic 62
  (1997).
* P. Pudlak, R. Impagliazzo, A lower bound for DLL algorithms for k-SAT, SODA 2000.
* A. Razborov, Lower bounds on the size of bounded depth circuits over a complete basis with logical addition, Math.
  Notes 41 (1987).
* A. Razborov, Unprovability of lower bounds on circuit size in certain fragments of bounded arithmetic, Izv. Math. 59
  (1995).
* A. Razborov, Lower bounds for the polynomial calculus, Comput. Complexity 7 (1998).
* A. Razborov, S. Rudich, Natural proofs, J. Comput. System Sci. 55 (1997).
* R. Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, STOC 1987.
* A. Tal, Shrinkage of De Morgan formulae by spectral techniques, FOCS 2014.
* G. S. Tseitin, On the complexity of derivation in propositional calculus, Studies in Constructive Mathematics and
  Mathematical Logic 2 (1968).
* A. Urquhart, Hard examples for resolution, J. ACM 34 (1987).
