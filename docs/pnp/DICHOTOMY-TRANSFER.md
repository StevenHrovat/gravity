# The worst-case dichotomy, transferred to refutations

Private working note, 2026-11-23. The owner asked: "This combined approach that worked for GRH and YM should also be
transferable to the current NP = coNP solve attempt." The approach is the Yang-Mills worst-case dichotomy
(`../mass-gap/weak-coupling/proof-phase/c9a-crossover/DICHOTOMY.md`, sections 0, 4 and 8) in four parts:
* (a) every piece of an obstruction either contracts (is local), or carries a conserved crossing flux, or is a residue
  inside one region;
* (b) local events behind a collar are attenuated: they enter only as a boundary term;
* (c) a conserved crossing flux cannot be screened;
* (d) what remains is a percolation question inside one region. Does the bad set span, or does it break into finite
  clusters with an exponential tail ("a well-defined non-existence inside a spanned existence")?

This note carries the four parts over to refutations, proves the exact ones in Lean, asks whether there is a family of
formulas whose crossing flux has no cheap name, relates that question to expansion, to formula-size lower bounds and
to the failure of interpolation, and stops at the first step that cannot be closed.

Claim marks as in `PROOF-SYSTEMS.md`. **[Lean]** here means `docs/mass-gap/formal/ProofPhase/Proof/` (new modules
`Crossing.lean` and `Complete.lean`, 35 declarations; `axioms-crossing.sh`, `axioms-crossing.log`; standard axioms
only, no `sorry`), on top of the four modules of `PROOF-SYSTEMS.md`.

---

## 0. The short answer

1. **The dichotomy transfers exactly, part by part.** Every line of a refutation is one of three kinds:
   * local: forced by a few constraints;
   * crossing: forced by a middle-sized region, which makes it sensitive to every variable on that region's boundary;
   * global.

   In **every** sound proof system whose rules have at most two premises (resolution, cutting planes, Frege,
   extended Frege), every refutation of an expanding formula contains a crossing line sensitive to at least the
   expansion many variables. **[Lean]** (`cross_any_system`)
2. **The conserved flux is proved conserved.** For Tseitin formulas Gauss's law holds mod 2: whatever the interior
   does, the parity crossing the boundary of a region equals the charge inside. It cannot be screened, and odd total
   charge is a contradiction. **[Lean]** (`gauss`, `flux_fixed`, `unsat_of_odd`)
3. **The crossing is universal, but its cost is not.** That cost is the price of **naming** the conserved quantity in
   the system's lines.
   * One exclusive-or names the whole Tseitin flux (**[Lean]**, `summary`). It costs resolution 2^(b-1) clauses of
     width b (**[Lean]**, the cut principle), and a Frege line about b^2 symbols.
   * Counting (the pigeonhole flux) is cheap for cutting planes and Frege and expensive for bounded-depth Frege.

   This is the proof-complexity counterpart of Yang-Mills part (a) failing: there the sheet cost vanishes at the
   SO(3) cut; here the crossing cost collapses to polynomial wherever the conserved quantity has a short name.
   **[classical]** + **[reading]**
4. **A family whose crossing flux has no cheap name.** One must look at a cut of the whole formula, not at one line.
   * Split the formula into two sides A(x, y) and B(x, z) that share only x. The crossing flux is the pair of
     **boundary laws**: beta_A(x) = "some y satisfies A", beta_B(x) = "some z satisfies B". They are disjoint
     because the formula is unsatisfiable.
   * "No cheap name" means no small formula separates them.
   * For crypto-built families such pairs exist under standard assumptions, **but Frege refutes those families
     anyway**. Feasible interpolation fails for Frege (Bonet-Pitassi-Raz 2000), so a short proof need not carry a
     separator.

   The candidate that avoids this is a family with no algebraic structure: **random 3-CNF at constant clause
   density**. There the bad set of the dichotomy (constraint sets that fail to expand) is exactly a "well-defined
   non-existence inside a spanned existence":
   * only finite clusters below a linear size, with a decaying tail;
   * the whole formula is unsatisfiable;
   * the clusters start to span only at densities near n^0.4 to n^0.5, where cheap refutations appear.

   **[classical]** + **[reading]**
5. **The first step that cannot be closed** (section 6) is the **transfer step T** for Frege on random 3-CNF:
   * the statement: every polynomial-size Frege refutation yields a polynomial-size formula separating the boundary
     laws of some balanced cut;
   * open; its general form, for all formulas, is false under factoring hardness, so a proof must use the absence of
     structure in a random formula;
   * behind it is **step H**: no such small separating formula exists. That is a formula lower bound of the kind that
     is open beyond about n^3.

   **[open]**

---

## 1. The four parts, side by side

| Yang-Mills (DICHOTOMY.md, (D'')) | Refutations | Status |
|---|---|---|
| a piece of the obstruction: a box configuration | a line of the refutation | definition |
| contracts / local | the line is forced by few constraints (`muL` small); it carries no global information | **[Lean]** measure; meaning **[classical]** (below) |
| crossing flux: forced sheet, `cob_restrict_eq_cob_restrict_compl` | the line is forced by a middle-sized region S and must see every boundary variable of S | **[Lean]** `exists_middleL`, `sensitive_of_boundary` |
| residue inside one box | constraint sets that fail to expand (too few boundary variables) | definition; **[Lean]** `unique_neighbors` links it to expansion |
| (b) attenuation behind a collar, condition A | small regions are satisfiable and their partial assignments extend; width equals a local-consistency game | **[classical]** (Atserias-Dalmau 2008; closure, Alekhnovich-Razborov) |
| (c) flux conserved, not screenable | Gauss's law mod 2 for Tseitin; for any cut, unsatisfiability is exactly disjointness of the two boundary laws | **[Lean]** `gauss`, `flux_fixed`; the cut statement is elementary |
| (d) near-cut set: spans at beta 2.3, isolated at 3.5 | non-expanding constraint sets: finite clusters at constant density, spanning at polynomial density | **[classical]** |
| part (a) fails uniformly: zero sheet cost at the SO(3) cut | crossing cost collapses where the conserved quantity has a short name (parity, counting) | **[classical]** |
| "well-defined outside" (the excluded set has positive weight) | "formulas whose crossing laws have no short name": the hypothesis that is open | **[open]** |

## 2. What is exact (Lean, `ProofPhase/Proof/Crossing.lean`)

**Conservation (part c).** A Tseitin system with every edge at exactly two vertices:

| Result | Statement |
|---|---|
| `gauss` | For every vertex set S and every assignment, the sum over S of the numbers of true edges at each vertex equals, mod 2, the number of true edges on the boundary of S. Interior edges count twice and drop out. |
| `flux_fixed` | If the constraints of S hold, the boundary parity equals the charge of S, **whatever the interior does**. |
| `unsat_of_odd` | Odd total charge: no assignment satisfies every vertex (S = all vertices has no boundary). |
| `summary` | The constraints of S force one line, "boundary parity = charge of S", which depends on the boundary edges only. A single exclusive-or carries the whole crossing flux. |

**The crossing step in every proof system (parts a and b).** `SD Ax L`: L is derivable from the constraint blocks by
sound rules with at most two premises. A line is read as the set of assignments that satisfy it, so this covers
resolution, cutting planes, Frege and extended Frege (modus ponens has two premises; one-premise rules repeat a
premise).

| Result | Statement |
|---|---|
| `muL_inf` | No inference creates assertion: the measure of a conclusion is at most the sum over its premises. The proof uses only soundness. |
| `exists_middleL` | Every refutation contains a line asserting a region of middle size. |
| `sensitive_of_boundary` | Such a line, for a smallest region, changes value when any boundary variable flips. |
| `cross_any_system`, `Tseitin.cross_any_system` | Under an expansion count e and satisfiable proper sub-systems, **every refutation in every such system contains a line sensitive to at least e variables.** |

**Expansion gives the crossing variables (parts b and d).**

| Result | Statement |
|---|---|
| `unique_neighbors` | 2 \|N(S)\| <= sum of \|I v\| over S + \|U(S)\|, where N(S) is the set of variables of the constraints in S and U(S) those that occur in exactly one of them. If constraints of at most k variables touch at least (k/2 + d)\|S\| variables, at least 2d\|S\| are unique: the toggle variables the cut principle needs. |

**What the exact part says.** The crossing is not optional: every proof system must, at some line, look at the whole
boundary of a middle-sized region. That is parts (a) and (c) of the dichotomy as theorems. What it does not say is how
much that line costs.

## 3. Where the cost collapses: naming the conserved quantity

Sensitivity to b variables costs a resolution line b literals: a clause sees only what it names. For the Tseitin
flux a resolution proof needs a clause for each of the 2^(b-1) wrong patterns of the boundary, so width b and, through
size-width, size exponential in b (`PROOF-SYSTEMS.md`, **[Lean]** for tree-like). A Frege line can be sensitive to b
variables at size about b, and it names the parity at size about b^2. So the cost of a crossing is the cost of
**naming** the conserved quantity in the line language:

| Conserved quantity | Example | Resolution | Cutting planes | Bounded-depth Frege | AC^0[2]-Frege | Frege |
|---|---|---|---|---|---|---|
| parity (mod 2 flux) | Tseitin | exp (Urquhart 1987) | short proofs known (recent work, not checked here) | exp on expanders (Ben-Sasson 2002) | cheap: parity gates | poly (Urquhart 1987) |
| counting | pigeonhole | exp (Haken 1985) | poly (Cook-Coullard-Turan 1987) | exp (Ajtai; KPW; PBI) | open | poly (Buss 1987) |
| none known (no algebraic structure) | random k-CNF, constant density | exp for k = 3 (Chvatal-Szemeredi 1988) | exp for k large enough (Fleming-Pankratov-Pitassi-Robere 2017; Hrubes-Pudlak 2017) | open in general | open | **open** |

**[classical]**. Entries marked open are open. The cutting-planes entry for Tseitin is a recent result whose exact
form is not checked here.

Every family on which Frege is known to be efficient has a conserved quantity that Frege names: parity, counting, or
more generally a quantity built from arithmetic Frege can carry. This is the counterpart of Yang-Mills part (a): the
uniform cost vanishes where the conserved quantity is free to name, as the sheet cost vanishes at the SO(3) cut.
**[reading]**

## 4. Looking for a family whose crossing flux has no cheap name

**Not a single line.** For one region S, the line "all constraints of S hold" is a cheap Frege line, and it is
forced by S. So no single-line argument can force cost in Frege: a line may carry the constraints themselves instead
of a summary of their boundary law. The cost has to come from the whole proof crossing a cut. **[reading]**,
elementary.

**The cut form of the flux.** Split the clauses into two sides A(x, y) and B(x, z) that share only the variables x.
* The **boundary laws** are beta_A(x) = "some y satisfies A" and beta_B(x) = "some z satisfies B".
* Exact: the formula is unsatisfiable exactly when beta_A and beta_B are disjoint. Everything one side tells the other
  passes through x (the Markov property of a CNF across a cut). This is part (c): the crossing flux is the pair of
  boundary laws, and no refinement of either side changes it. **[classical]**, elementary
* A **separator** is any I(x) with beta_A inside I and I disjoint from beta_B. **Feasible interpolation** for a
  system: a refutation of size s yields a separator of size poly(s) in some circuit class. **[classical]**
  * Resolution: circuits (Krajicek 1997).
  * Cutting planes: monotone real circuits (Pudlak 1997).

**The two requirements for a Frege lower bound by this route.**
* **H (hard flux):** the boundary-law pair of every balanced cut has no polynomial-size separating formula.
* **T (transfer):** every short Frege refutation yields a short separating formula for some balanced cut.

**The tension.** For crypto-built families, H holds under standard assumptions. The pair "x encodes a factorization
with bit i = 0" against "... with bit i = 1" has no small separator if factoring is hard. **But T fails on exactly
those families:** Frege proves their disjointness in polynomial size by arithmetic reasoning, without the proof
carrying a separator (Bonet-Pitassi-Raz 2000; Krajicek-Pudlak 1998 for extended Frege). So the structure that makes
the flux hard to name is also the structure that lets Frege reason around it. **[conditional]**

**The way out: no structure.** A family where H is plausible and the crypto counterexample to T does not apply is one
without algebraic structure: **random 3-CNF with m = Delta n clauses, Delta a large constant** (above the
satisfiability threshold, about 4.27, so unsatisfiable with high probability). **[reading]** for the choice; it is also
the standard conjecture in the field.

**The dichotomy's part (d) on random 3-CNF.** Here the bad set is the constraint sets that fail to expand (fewer than
(1.5 + d)|S| variables, hence few unique variables by `unique_neighbors`).
* **Finite clusters with a tail (constant density).** With high probability every set of at most epsilon n clauses
  expands (Chvatal-Szemeredi 1988; Ben-Sasson-Wigderson 2001). A given set of size s fails with probability that
  decays in s, so no deficient set exists below linear size. In the owner's terms: a well-defined non-existence inside
  a spanned existence.
  * Spanned existence: the whole formula is unsatisfiable.
  * Well-defined non-existence: every part below linear size is satisfiable, and the deficient sets do not percolate
    below that size.

  **[classical]** + **[reading]**
* **Spanning at polynomial density.** As Delta grows the expansion weakens.
  * Resolution lower bounds persist up to about n^(1/2 - epsilon) for 3-CNF (Beame-Karp-Pitassi-Saks 2002;
    Ben-Sasson-Wigderson 2001).
  * Polynomial-size refutations appear once the global spectral structure can be summarized: spectral refutation at
    about n^1.5 clauses, and polynomial-size witnesses from about n^1.4 clauses (Feige-Kim-Ofek 2006).

  This is the transition of part (d): when the residue spans, a cheap global summary of the flux exists, as the
  near-cut set spanning the box at beta = 2.3 made a sheet nearly free. **[classical]** (the thresholds, as recalled
  here) + **[reading]**
* **Known for random k-CNF:** exponential lower bounds for resolution and polynomial calculus (k = 3), and for cutting
  planes (k large enough). All of
  them pass through expansion: (b) and (d) of the dichotomy. **Open:** Frege.

## 5. Relation to expansion, to the formula-size bound, and to the failure of interpolation

* **Expansion** is the dichotomy's collar and its residue at once.
  * As the collar (b): small regions are satisfiable, and a partial assignment of small support extends. A local line
    carries no information about the contradiction, and width equals the local-consistency game (Atserias-Dalmau).
  * As the residue bound (d): no deficient set below linear size.
  * Its exact consequences here: `unique_neighbors` (expansion gives toggle variables), the cut principle (width is at
    least the boundary) and `cross_any_system` (every system must cross).

  **[Lean]** + **[classical]**
* **The formula-size bound** is step H. Even for an explicit family it would be a superpolynomial formula lower bound
  for a pair of NP sets (the boundary laws are NP predicates). For one explicit NP function that already means NP is
  not contained in non-uniform NC^1, and the best explicit formula lower bounds are about n^3 (Hastad 1998, Tal 2014).
  For random 3-CNF the pair is not explicit, so counting arguments are not excluded. But the boundary laws of a random
  formula are far from uniformly random functions, and no lower bound for them is known. **[classical]** (the
  implication), **[open]** (H)
* **The failure of interpolation** is step T. Under factoring hardness, T is false for Frege in general
  (Bonet-Pitassi-Raz). Any proof of T for random 3-CNF must therefore use the absence of structure, a property of the
  input that no known technique turns into a statement about Frege proofs. **[conditional]** (the failure), **[open]**
  (T for random formulas)

## 6. The first step that cannot be closed

**Step T (transfer for Frege on random 3-CNF).** For Delta a large constant and F a random 3-CNF with Delta n clauses,
with high probability:

> every Frege refutation of F of size s yields a formula of size poly(s) that separates the boundary laws of some
> balanced cut of F.

* Status: **[open]**.
* Why it cannot be closed with the tools at hand: the only known transfer is feasible interpolation, and it is false
  for Frege on structured inputs unless factoring Blum integers is easy. A proof of T must use that F has no such
  structure. No known method connects the randomness of the input to the shape of an arbitrary Frege proof.
* Behind it, **step H**: with high probability no polynomial-size formula separates those boundary laws. It is also
  **[open]**, a formula lower bound beyond the current n^3 barrier, for a random but NP-definable pair.

T and H together would give superpolynomial Frege lower bounds for random 3-CNF. That is far from NP != coNP, since
extended Frege and every stronger system would remain.

**Known steps not formalized in Lean:**
* the DAG-like size-width relation;
* the probabilistic expansion of random 3-CNF;
* feasible interpolation for resolution;
* satisfiability of proper Tseitin sub-systems on connected graphs.

**In the dichotomy's own terms.** Part (a) fails uniformly for Frege, for the same structural reason as in Yang-Mills:
there is a "cut" (a short name for the conserved quantity) where the crossing cost vanishes. The repair the owner
proposed for Yang-Mills, uniformity over every well-defined outside, has the counterpart "uniformity over formulas
whose crossing laws have no short name". Making that class precise and proving it non-empty is step H. Showing that
Frege cannot avoid it is step T.

## 7. DMP reading (separate, marked)

Everything here is **[reading]** unless marked otherwise.

* **"Existence defined by its non-existence; both created together."** A refutation is the created description of a
  non-existence. The dichotomy says where its cost sits: not in the local lines, which are attenuated behind the collar
  of expansion, but in the crossing, where the assertion of a middle region has to pass its boundary. That crossing is
  forced in every proof system (`cross_any_system`, **[Lean]**).
* **"The remnant of a flux act is carried through the DB intact, not worn down"** (DICHOTOMY.md 8.6). Gauss's law mod 2
  is this statement for Tseitin formulas, **[Lean]** (`flux_fixed`): the boundary parity is fixed by the charge inside,
  whatever the interior does.
* **"Only existence crosses; information is radiated as loss."** In a Tseitin refutation, what has to cross is one bit
  per region: the binary existence datum. A system that can name that bit (Frege, by an exclusive-or) crosses for
  free. A system that cannot (resolution) must carry all the information the bit summarizes, and pays exponentially.
  So the owner's binary-existence picture predicts both the hardness for resolution and the ease for Frege.
* **What a hard family would have to look like.** Its crossing datum is not one bit with a short name. Its boundary
  laws carry existence that no short description summarizes, and the formula has no algebraic structure that would let
  a strong system reason around the boundary. In DMP terms: a spanned existence (globally unsatisfiable) whose
  non-existence is well defined (finite deficient clusters) but whose boundary assertion has no compact encoding in the
  universal language. Random 3-CNF at constant density is the natural candidate. Whether its boundary assertions have
  compact encodings is step H, and whether Frege must produce them is step T.
* **"A refutation can not travel upward ... for existence to be, it has to be refutable"** (the owner, same day,
  verbatim): "I would assume a bad proof would have to be isolated at a fundamental level, spanning a boundary over the
  associated question that only presents the answer false. Since the question can only be constructed in a
  DMP-complete way, it must be built from things that are fundamentally true, so a refutation can not travel upward.
  The record of the act is the discovery of the fact that this is an answerable question which happens to be false. As
  such it also defines it as the act itself, since for existence to be, it has to be refutable." Each clause of the
  reading maps to a statement:

  | The owner's words | Statement | Level |
  |---|---|---|
  | "a refutation can not travel upward" | **Soundness:** from a satisfiable formula no derivation reaches the contradiction (`TL.unsat`, `WD.exists_falsified`, `SD.impliesL_univ`: every line is forced by the axioms). Quantitative half: **no inference creates assertion** (`muL_inf`); a line can assert a region only by resting on the parts of it, so assertion climbs only by accumulating. | **[Lean]** |
  | "for existence to be, it has to be refutable" | **Refutation completeness:** every unsatisfiable formula has a resolution refutation (`complete`); with soundness, refutable exactly when unsatisfiable (`refutable_iff`). The refutation is the record of the act. | **[Lean]** (new, `Complete.lean`) |
  | "built from things that are fundamentally true" | Every proper sub-system is satisfiable (the hypothesis `hsat`): the formula is minimally unsatisfiable. | definition |
  | "isolated at a fundamental level ... only presents the answer false" | Then the contradiction asserts the **whole** question (`mu_empty`; the `muL` version inside `cross_any_system`): no part of the question is false by itself, and the falsity exists only at the level of the whole. | **[Lean]** |
  | "spanning a boundary over the associated question" | The cut principle: some line asserts a middle-sized region and is sensitive to its whole boundary, in every proof system (`cross_any_system`); in resolution it pays one literal per boundary variable (`width_ge`). | **[Lean]** |
  | "the record of the act is the discovery that this is an answerable question which happens to be false" | A refutation is a certificate checkable in time polynomial in its own length; the question is decidable, and the certificate is the record. | **[classical]** |

  **What this adds to the size question, plainly.**
  * **Soundness and completeness add nothing to it.** Both hold for every proof system by definition, short ones and
    long ones alike. The completeness proof here builds refutations of up to 2^n leaves: the record of the act exists,
    and nothing in the reading says it is short. Whether every such record can be short is NP = coNP, and the two
    facts are equally true whether NP = coNP or not.
  * **Minimality ("built from fundamentally true things") adds a usable hypothesis.** It forces every refutation to
    assert the whole question at its root, which is what makes the middle line, and hence the crossing, unavoidable.
    It does not bound the cost of the crossing.
  * **"Spanning a boundary" locates the cost but does not price it.** The cost is the price of naming what crosses.
    For resolution that price is exponential (proved). For Frege it is polynomial whenever the crossing datum is a
    parity or a count. Whether some family's crossing datum has no short name in any proof language is steps H and T
    of section 6, unchanged by this reading.
  * **In one sentence:** the reading is correct as a description of what a refutation is and where its cost sits;
    the open step is the size of the record, and the reading gives no lower bound on it.
* **What DMP adds, and what it does not.** It predicts the right split: local lines attenuated, crossing forced, cost
  equal to the encoding cost of the crossing datum. That split is proved where it is exact. It does not supply an
  encoding lower bound, which is a circuit-complexity question, and it names no mechanism for step T.

## 8. Status

| Step | Level |
|---|---|
| Gauss's law mod 2, the crossing flux fixed by the inside, Tseitin's contradiction | **[Lean]** |
| One exclusive-or carries the Tseitin flux | **[Lean]** |
| Soundness and refutation completeness of resolution (refutable exactly when unsatisfiable) | **[Lean]** |
| No inference creates assertion; a middle line exists in every sound two-premise system | **[Lean]** |
| The crossing line is sensitive to every boundary variable; every system must cross (expansion e) | **[Lean]**, hypotheses: expansion count, proper sub-systems satisfiable |
| Expansion gives unique (toggle) variables | **[Lean]** |
| Width at least boundary, tree-like size exponential (from `PROOF-SYSTEMS.md`) | **[Lean]** |
| Crossing cost by line language (table of section 3) | **[classical]** |
| Cut form: unsatisfiable exactly when the boundary laws are disjoint | **[classical]**, elementary |
| Feasible interpolation for resolution and cutting planes | **[classical]** |
| Its failure for Frege and extended Frege | **[conditional]** (factoring, RSA) |
| Random k-CNF: expansion below linear size; hard for resolution, polynomial calculus (k = 3), cutting planes (k large) | **[classical]** |
| Step T for Frege on random 3-CNF | **[open]**, first unclosed step |
| Step H, formula-size separation of the boundary laws | **[open]** |

## 9. References

In addition to those of `PROOF-SYSTEMS.md`:

* A. Atserias, V. Dalmau, A combinatorial characterization of resolution width, J. Comput. System Sci. 74 (2008).
* M. Alekhnovich, A. Razborov, Lower bounds for polynomial calculus: non-binomial case, Proc. Steklov Inst. Math. 242
  (2003).
* E. Ben-Sasson, Hard examples for bounded depth Frege, STOC 2002.
* P. Beame, R. Karp, T. Pitassi, M. Saks, The efficiency of resolution and Davis-Putnam procedures, SIAM J. Comput. 31
  (2002).
* S. Buss, Polynomial size proofs of the propositional pigeonhole principle, J. Symbolic Logic 52 (1987).
* W. Cook, C. Coullard, Gy. Turan, On the complexity of cutting-plane proofs, Discrete Appl. Math. 18 (1987).
* U. Feige, J. H. Kim, E. Ofek, Witnesses for non-satisfiability of dense random 3CNF formulas, FOCS 2006.
* A. Razborov, Pseudorandom generators hard for k-DNF resolution and polynomial calculus resolution, Ann. of Math. 181
  (2015).
