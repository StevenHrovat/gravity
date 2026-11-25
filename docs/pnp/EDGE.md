# The edge: cutting planes on random 3-CNF

Private working note, 2026-11-23. The owner asked to "proceed with our effort toward the final 3MP paper goal, so that
we can work on the edges and get better theories". The P vs NP edge is a concrete new lower bound on a structureless
family, guided by the owner's reading (PREP.md, "Three answers to the open questions", item (c)): "A question with no
structure has no basis/language in which to speak an answer and be sure it is understood."

The note does four things:
* picks the proof system (section 1);
* states the target (section 2);
* runs the crossing argument of `DICHOTOMY-TRANSFER.md` on it and shows where incompressibility enters (section 3);
* stops at the first step that cannot be closed (section 4).

Claim marks as in `PROOF-SYSTEMS.md`:
* **[Lean]** means `docs/mass-gap/formal/ProofPhase/Proof/`. Two modules are new here, both with standard axioms
  only and no `sorry`, on top of the modules of the earlier notes:
  * `Edge.lean`, 9 declarations (`axioms-edge.sh`, `axioms-edge.log`);
  * `Dag.lean`, 15 declarations (`axioms-dag.sh`, `axioms-dag.log`).
* **[classical]** marks published results, as recalled and, where marked, checked against the papers' abstracts on
  2026-11-23.
* **[reading]** marks interpretation.
* **[open]** marks unknown statements.

---

## 0. The short answer

1. **The system: cutting planes (CP); the family: random 3-CNF.** CP is the strongest system in which random CNF is
   known to be hard **only when the clauses are wide enough**: width Theta(log n) is solved, constant width is open. So
   the open part is exactly the structureless, constant-width case that item (c) is about. The other candidates are
   either solved (polynomial calculus, sum-of-squares degree) or open for every formula, structured or not (Res(xor),
   bounded-depth Frege with parity gates). In those, randomness is not the obstacle. **[classical]** + **[reading]**
2. **Target** (section 2). For a large constant Delta and a random 3-CNF F with Delta n clauses: with high
   probability, every CP refutation of F has size 2^(n^Omega(1)). **[open]**
3. **What closes** (section 3).
   * **Incompressibility of the specific formula gives expansion.** A formula with a small clause set that spans too
     few variables can be described in fewer bits than its length, so an incompressible formula has none. This is the
     one place where the absence of structure enters, and it is a statement about the one input, not about typical
     Boolean functions. So natural proofs do not bite. **[classical]** (the counting) + **[reading]** (the form)
   * **Expansion forces the crossing in CP.** Every CP refutation contains a line sensitive to Omega(n) variables
     (`cross_any_system`, **[Lean]**, from `Crossing.lean`; CP is covered because its rules are sound and have at most
     two premises).
4. **Where it stops** (section 4).
   * In resolution, the next step turns "a line sensitive to e variables" into size: the line is a clause of width e,
     and any one literal kills it under a restriction.
   * In CP that step is false. One CP line, the majority inequality "at least half of these e variables are true", is
     sensitive to all e of them and survives every restriction of fewer than e/2 variables (`majority_line`,
     **[Lean]**).
   * **The first unclosable step** is a cost measure on CP lines with two properties: the crossing forces it on every
     refutation of an expanding 3-CNF, and it is expensive in size.
   * The known substitutes do not supply it at width 3. Interpolation and dag-like communication need clauses that
     carry about log n bits. Rank lower bounds constrain depth, not size.
5. **What this adds:**
   * a sharp localisation: for CP on random 3-CNF the crossing is forced (Lean), and it is speakable in one line
     (Lean). The whole difficulty is converting a speakable crossing into proof size;
   * the reason the log n case works and the width-3 case does not, in one sentence: there the clause carries enough
     "language" for a gadget, here it does not (section 4).

   **No new lower bound.**
6. **The owner's lower bound, in two terms** (section 6): confinement (the amount the crossing must assert) times
   resolution (the share of it that one restriction resolves).
   * In resolution both terms are bounded, and the DAG-like size-width relation is now in Lean (`Dag.lean`):
     * size >= exp(b (w + d + 1) / 2n) whenever width w + d + b is impossible;
     * with the cut principle, size >= exp((e - w)^2 / 8n), up to rounding.
   * In CP, Res(xor) and Frege the restriction form of the uncertainty term collapses: one line can aggregate its
     units (counting, parity, anything). For Tseitin a single parity carries the whole crossing, one bit for e units.
   * W_CP is the missing uncertainty term for CP.

---

## 1. Picking the system

| System | Random 3-CNF (constant density) | Verdict |
|---|---|---|
| Resolution | exp(Omega(n)) (Chvatal-Szemeredi 1988; Ben-Sasson-Wigderson 2001) | solved |
| Polynomial calculus, any field | degree Omega(n), hence size exp(Omega(n)) (Ben-Sasson-Impagliazzo 1999; Alekhnovich-Razborov 2003) | solved |
| Sum-of-squares | degree Omega(n) (Grigoriev 2001; Schoenebeck 2008) | solved (degree) |
| Res(k), k-DNF lines | exponential for small k, up to about sqrt(log n / log log n) (Alekhnovich 2005/2011) | partly solved; open for k of order log n |
| Res(xor), linear clauses over GF(2) | no superpolynomial bound for **any** formula in the unrestricted system. Depth-restricted bounds exist (Efremenko-Itsykson; Alekseev-Itsykson; Bhattacharya-Chattopadhyay 2025, depth up to N^(2-eps), for lifted Tseitin) | open for every family |
| Bounded-depth Frege | bounds for pigeonhole and Tseitin, none for random 3-CNF beyond Res(k) | open |
| Bounded-depth Frege with parity gates | no bound for any formula | open for every family |
| **Cutting planes** | 2^(n/polylog n) for random Delta-CNF with Delta = Theta(log n) (Fleming-Pankratov-Pitassi-Robere 2017; Hrubes-Pudlak 2017); tight 2^Omega(n) (Sokolov, STOC 2024). Randomized communication of falsified-clause search is linear for random O(log n)-CNF (Riazanov-Sofronova-Sokolov-Yuan 2025). **Constant Delta: open** | **chosen** |

All entries are **[classical]**. The CP row and the Res(xor) row were checked against the abstracts on 2026-11-23. The
Res(k) range is as recalled.

**Why CP.**
* In Res(xor) and with parity gates, nothing is known even for structured formulas. A random family would not be the
  obstacle there; the system is.
* In CP the structured cases are known:
  * pigeonhole-type and clique-colouring formulas, by feasible interpolation with monotone real circuits (Pudlak 1997);
  * random CNF at width log n.

  What is missing is precisely the structureless, constant-width case. Item (c) predicts that the difficulty sits
  there, and it does. **[reading]**
* Tseitin formulas are **not** a candidate for CP. They have quasi-polynomial CP refutations (Dadush-Tiwari 2020), so
  random Tseitin on expanders is ruled out. **[classical]**
* Rank (depth) is known. Random k-CNF needs near-linear CP rank (Buresh-Oppenheim, Galesi, Hoory, Magen and Pitassi,
  FOCS 2003). **Depth is solved; size is open.** **[classical]**

## 2. The target

**Target.** Fix a large constant Delta. Let F be a random 3-CNF on n variables with Delta n clauses (unsatisfiable
with high probability above the threshold, about 4.27). With high probability, every CP refutation of F has size at
least 2^(n^c) for some c > 0. **[open]**

Even a superpolynomial bound would be new. It would be the first CP lower bound for a constant-width random formula,
and it would close the gap between width 3 and width log n left by the 2017 and 2024 results.

## 3. The attempt: what closes

### Step 1: incompressibility of the instance gives expansion

**Expansion** here: every set S of at most eps n clauses spans at least (3/2 + delta)|S| variables. By
`unique_neighbors` (**[Lean]**, `Crossing.lean`), such an S then has at least 2 delta |S| variables that occur in
exactly one of its clauses: its **boundary**, or toggle, variables.

**Where incompressibility enters.** Describe F as a list of Delta n clauses, each one of 8 C(n, 3) possibilities.
Suppose F has a deficient set S: s clauses spanning only t = (3/2 + delta) s variables. Then F can be written down as:
* the positions of S among the clauses: log C(Delta n, s) bits;
* the t variables: log C(n, t) bits;
* the s clauses of S as triples inside those t variables: about 3 s log t bits;
* the other clauses as usual.

Against the plain description of the s clauses (about 3 s log n bits), the saving is about
(1/2 - delta) s log(n/s) - O(s log Delta). For s <= eps n, with eps small enough in terms of Delta and delta, this is
at least of order log n.

So **every formula whose description cannot be shortened by that many bits is an expander.** Incompressible formulas
are the overwhelming majority, which is the Chvatal-Szemeredi union bound read as a compression argument.
**[classical]** (the counting, as in Chvatal-Szemeredi and Ben-Sasson-Wigderson; constants not optimized here) +
**[reading]** (the per-instance form)

**Why the natural-proofs barrier does not bite here.** That barrier is about a property of Boolean functions used
to show they lack small circuits; a pseudorandom function would fool such a property. Step 1 uses instead a property
of the **one input formula** (no small clause set describes itself cheaply) to constrain **all proofs of that
formula**.

The resolution and the log-n CP lower bounds use exactly this step and are unconditional, so the step itself is safe.
The barriers that exist in proof complexity (failure of feasible interpolation under cryptographic assumptions,
`DICHOTOMY-TRANSFER.md` section 4) concern systems stronger than CP. CP has feasible interpolation. **[classical]** +
**[reading]**

### Step 2: the crossing is forced in CP

CP lines are integer inequalities over 0/1 variables. Its rules are:
* addition (two premises);
* multiplication by a positive integer (one premise);
* division with rounding (one premise);
* the axioms 0 <= x <= 1 and the clauses written as inequalities.

Every rule is sound for 0/1 assignments and has at most two premises. So every CP refutation is a derivation `SD` in
the sense of `Crossing.lean`, and `cross_any_system` applies (**[Lean]**). With the expansion of step 1,
every CP refutation of F contains a line L that:
* is forced by a middle-sized region S of clauses (between eps n / 2 and eps n);
* is sensitive to each of the at least 2 delta |S| = Omega(n) boundary variables of S. Flipping such a variable
  changes L at some assignment.

This step closes. Up to here CP and resolution behave the same.

## 4. Where it stops: the first unclosable step

### What resolution does next

A resolution line sensitive to e variables is a clause of width at least e (`Cut.lean`). A clause is killed, made
true, by fixing any one of its literals (`clause_killed`, **[Lean]**). That is the engine of the size-width
relation (`SizeWidth.lean`; Ben-Sasson-Wigderson):
* a short proof has few wide clauses;
* fixing the most frequent literal kills a fixed fraction of them;
* repeating this removes them all while expansion survives;
* the result is a narrow refutation, which the crossing forbids.

### Why the same step is false in CP

`majority_line` (**[Lean]**, `Edge.lean`): for every nonempty set B of variables, the single CP line

> x_1 + ... + x_|B| >= |B|/2 + 1  (over the variables of B; `thr`, `thr_iff_cp`)

* is sensitive to **every** variable of B (`thr_sensitive`);
* survives every restriction of fewer than |B|/2 variables: whatever values they get, some extension still falsifies
  it (`thr_survives`).

So one CP line can carry the whole crossing, and the restriction step has nothing to remove. In resolution the same
line costs about 2^|B| / sqrt|B| clauses (**[classical]**, elementary), which is why width there means size.

### The unclosable step, stated

> **Step W_CP.** Find a measure nu on CP lines such that:
> (i) every CP refutation of an expanding 3-CNF contains a line with nu >= n^Omega(1), forced by the crossing of
> step 2; and
> (ii) a CP refutation of size s has a line of nu that large only if s >= 2^(n^Omega(1)). This could come, for example,
> from a random restriction or projection that preserves expansion and lowers nu in every line.

**[open]**

`majority_line` shows that "number of variables a line is sensitive to" is not such a nu: (i) holds and (ii) fails.
Each known substitute fails at width 3 for a stated reason.

* **Interpolation and dag-like communication.** This is the route that works at width log n:
  * monotone real circuits (Pudlak 1997);
  * dag-like real or triangle protocols for the falsified-clause search (Fleming-Pankratov-Pitassi-Robere;
    Hrubes-Pudlak; Sokolov 2024);
  * the randomized version (Riazanov-Sofronova-Sokolov-Yuan 2025, which assumes Delta >= c log n).

  Each splits the variables between two players and needs every clause to carry enough bits on both sides to act as a
  gadget. At width 3:
  * under any split, a constant fraction of clauses lies wholly on one side (a quarter under a random split);
  * each clause carries O(1) bits;
  * current dag-like lifting needs gadgets of about log n bits.

  **[classical]** (that the known proofs need Delta of order log n) + **[reading]** (the reason in these words)
* **Rank.** Random k-CNF needs near-linear CP rank (Buresh-Oppenheim et al.). Rank counts layers, not lines. The
  native-method finding applies directly: depth can be contracted while the total work is conserved (`pairUp`,
  `ProofPhase/Native/Method.lean`), so a depth bound alone says nothing about size. **[classical]** + **[Lean]**
  (the pointer-jumping fact)

So the attempt stops at W_CP. Steps 1 and 2 hold for CP as for resolution. The missing piece is a single
size-sensitive measure that is forced by expansion of a constant-width formula.

**Known results checked against the target:** none covers it. The closest are the width-log-n bounds and the rank
bound, and neither reaches constant width in size. So no fallback to the next system was needed.

## 5. DMP reading (separate, marked)

Everything here is **[reading]** unless marked otherwise.

* **"A question with no structure has no basis/language in which to speak an answer."** For a refutation, the
  question is "does this formula's world exist?". Incompressibility makes the formula structureless in a precise
  sense: no small part of it has a short self-description (step 1). Its consequence is expansion: every small part
  has many boundary variables, and a local line can say nothing about the contradiction. The non-existence can only be
  spoken at a crossing, by a line that names Omega(n) boundary variables (step 2, **[Lean]**).
* **The language is the proof system's, not the formula's.** The formula has no language for its non-existence, but
  each proof system brings one.
  * Resolution has only clauses. Naming e variables costs e literals, and restrictions make such lines many.
  * CP has counting. One inequality names all e variables at once and survives every small restriction
    (`majority_line`, **[Lean]**).

  So the answer can be **spoken** cheaply in CP.
* **"... and be sure it is understood."** This half is the open one. In proof terms, "understood" is derivability:
  the line must follow from earlier lines by the rules, and the refutation must reach the empty line. `majority_line`
  measures only speaking. The missing measure nu of W_CP would measure the cost of being understood: of deriving a
  crossing line, not of writing it. Item (c), read this way, says where the open problem sits: between speaking the
  crossing and having it understood.
* **Width log n against width 3.** At width log n each clause carries about log n bits, enough "language" inside one
  clause to hold a gadget. That is what the known proofs use. At width 3 a clause carries O(1) bits: the structureless
  limit, where no single clause has a language of its own. **[classical]** (the threshold of the known proofs) +
  **[reading]**
* **"An empty set at least has the base definition for existence."** The compression argument of step 1 starts from
  the plain count of all formulas, the base description against which a structured formula is shorter. Expansion is
  the statement that F is not shorter than that base. **[reading]**

* **"The confinement bound plus the needed uncertainty ... transferrable to all DMP subsets."** The two-term form is
  a schema that does not depend on the system (section 6 (a)).
  * The confinement half is universal and in Lean (`cross_any_system`).
  * The uncertainty half depends on the subset's language: how many units a single assertion can aggregate.
  * Where the language spells its units out one by one (clauses, monomials), the bound follows (`Dag.lean`,
    **[Lean]**).
  * Where it can aggregate (counting, parity), the uncertainty per unit drops to the information the crossing actually
    carries, one bit for a Tseitin region, and the bound is lost.

**What the DMP reading adds here:** a name for the gap, "spoken versus understood", that matches the technical gap
(sensitivity versus derivation cost). **It does not supply nu.**

## 6. The lower bound in two terms: confinement times resolution

The owner asked for the lower bound that DMP gives for optimization: "the confinement bound plus the needed
uncertainty that is generated by the amount and resolution of its accompanying assertion", which carries over to all
DMP subsets. This section does three things:
* states the bound for proof systems in general;
* proves the resolution instance in Lean, DAG-like (the step listed as not formalized in `DICHOTOMY-TRANSFER.md`,
  section 6);
* says where each term can be bounded.

### (a) The general form

Take a proof system, a family of formulas and a family of **restrictions** (partial assignments, or projections).
Each restriction must map a refutation of F to a refutation of the restricted formula, no larger. Two quantities
enter.

1. **Confinement c (the amount).** Every refutation contains a line whose assertion has at least c units, counted in
   the system's own unit: clause width, monomial degree, or number of boundary variables named.
   * Its source is expansion through the crossing: `cross_any_system` (**[Lean]**) forces, in every system, a line
     sensitive to e boundary variables.
   * The unit cost of that line is the confinement.
   * It is an area law: the cost grows with the boundary the line must assert.
2. **Resolution rho (how finely the assertion is spelled out).** This is the share of lines of at least c units that
   one restriction step removes, while the restricted formula keeps its confinement up to one unit.
   * A line that names each of its c units separately is caught by any one of them.
   * With N units available, a random or most frequent unit hits such a line with share about c / N.

**The bound.** If the confinement survives b restriction steps, the size is at least (1 - rho)^(-b) >= exp(rho b).
With rho about c / N and b about c:

> log(size) >~ c * (c / N) = confinement x resolution.

In the width itself the terms add, which is the owner's "plus". The width a refutation needs is at most w + d + b,
where:
* w is the axiom width (the base);
* d is the confinement threshold (lines above it count as fat);
* b is the number of restriction steps (the uncertainty that is resolved one unit at a time).

**[reading]** for the general schema; **[Lean]** for the resolution instance below.

### (b) The resolution instance, in Lean (`Dag.lean`, 15 declarations)

* `RD F P C`: DAG-like derivations by resolution and weakening, with every line in the finite set P. A DAG-like
  refutation whose distinct lines form P gives `RD F P` of the empty clause, so |P| is at most its size.
* `RD.restr`: fixing a literal maps a derivation from F to one from the restricted formula, with lines `rP`. Lines
  containing the literal vanish.
* `exists_heavy` (**confinement**, by double counting): if every fat line has more than T literals, some literal lies
  in at least a (T + 1) / |L| share of the fat lines.
* `card_fat_rP_le` (**resolution**): fixing that literal removes that share. `step_arith` is the arithmetic of one
  step.
* `size_width`: let F have axioms of width at most w and n variables, and no refutation of width w + d + b. Then
  every DAG-like refutation satisfies (2n)^b <= |P| (2n - (w + d + 1))^b.
* `size_width_exp`: hence exp(b (w + d + 1) / 2n) <= |P|.
* `dag_size_ge`: the same bound for every block system whose middle regions have e boundary variables, whenever
  w + d + b < e, by the cut principle (`width_ge`, `Cut.lean`).
  * With d = b about (e - w)/2 this gives |P| >= exp((e - w)^2 / (8n)), up to rounding.
  * That is the Ben-Sasson-Wigderson form exp(Omega((e - w)^2 / n)): confinement e, squared, over the number of
    units n.

Standard axioms only (`axioms-dag.sh`, `axioms-dag.log`). Together with `Cut.lean` and `Crossing.lean`, the chain
expansion -> crossing -> width -> DAG-like size is now in Lean for resolution. The one missing piece is the
probabilistic expansion of a random formula (section 3, step 1).

### (c) Where both terms can be bounded, and where the uncertainty term collapses

| System | Confinement (unit) | Resolution (what kills a line) | Both bounded? |
|---|---|---|---|
| Resolution | width | fixing one literal kills a clause; share c / 2n | **yes**, **[Lean]** (`Dag.lean`) |
| Polynomial calculus | degree | fixing a variable kills the monomials containing it; size >= exp(Omega((D - d0)^2 / n)) (Impagliazzo-Pudlak-Sgall 1999) | **yes**, **[classical]** |
| Res(k), small k | k-DNF lines | random restriction plus switching lemma: a k-DNF collapses to a short decision tree | **partly**: k up to about sqrt(log n / log log n) on random 3-CNF, **[classical]** |
| Bounded-depth Frege | depth-d formulas | Hastad's switching lemma | **yes** for pigeonhole and Tseitin (Ajtai; Krajicek-Pudlak-Woods; Pitassi-Beame-Impagliazzo; Pitassi-Rossman-Servedio-Tan; Hastad), **[classical]**; open for random 3-CNF |
| Cutting planes | boundary variables named | **none by restriction**: the majority line survives every restriction of fewer than e/2 variables (`majority_line`, **[Lean]**) | confinement **yes** (Lean); resolution only through interpolation at width log n; open at width 3 (W_CP) |
| Res(xor) | boundary variables named | **none by restriction**: a parity over B survives while one variable of B is free | **collapses** on Tseitin: one parity carries the crossing (`summary`), and Gaussian elimination refutes in polynomial size, **[classical]** |
| Frege | boundary variables named | **none**: any function of the boundary is one line | **collapses** on Tseitin: polynomial-size refutations (Urquhart 1987; Buss), **[classical]**; open for random 3-CNF |

**The collapse, stated plainly.** The uncertainty term counts the information the crossing line must carry per unit
of boundary.
* A clause carries one literal per unit. To be true it must name each unit, and any unit fixed the right way kills
  it. That is a full share per unit, and the term is c / N.
* A Tseitin crossing carries **one bit in total**: the boundary parity, which equals the charge inside (`flux_fixed`,
  **[Lean]**). A system that can write a parity names e units with one bit, so the information per unit is 1/e and
  goes to 0. Confinement is still forced (`cross_any_system`), but it costs nothing. This happens in Res(xor) and in
  Frege.
* **The general rule (**[reading]**):** the uncertainty term is bounded below exactly when the system's lines are
  local for some family of restrictions.
  * Local means that fixing a small part of what a line asserts kills it: clauses, monomials, and small-depth
    formulas after switching.
  * The term collapses when one line can aggregate its units: counting in CP, parity in Res(xor), anything in Frege.
    A lower bound then needs a resolution measure that is not restriction-based. For CP at width log n that is
    interpolation; for Res(xor) and Frege none is known.

**For the edge.** CP on random 3-CNF is the case where confinement is forced and the restriction form of the
uncertainty term provably collapses, both in Lean. W_CP (section 4) is exactly the missing uncertainty term for CP:
an information-per-unit measure on CP lines that a counting inequality cannot evade.

## 7. Status

* **[Lean]** (`Edge.lean`, 9 declarations): `clause_killed`, `thr`, `thr_iff_cp`, `ind`, `filter_ind`, `flip_ind`,
  `thr_sensitive`, `thr_survives`, `majority_line`. Standard axioms only (`axioms-edge.log`).
* **Used from earlier notes, [Lean]:** `cross_any_system`, `unique_neighbors` (`Crossing.lean`); the cut principle
  (`Cut.lean`); size-width for tree-like resolution (`SizeWidth.lean`); `pairUp` (`Native/Method.lean`).
* **[Lean]** (`Dag.lean`, 15 declarations): `RD`, `rP`, `fat`, `mem_rP`, `RD.toWD`, `RD.nl_inj`, `RD.restr`,
  `card_fat_rP_le`, `exists_heavy`, `step_arith`, `thin`, `size_width_aux`, `size_width`, `size_width_exp`,
  `dag_size_ge`. Standard axioms only (`axioms-dag.log`).
* **Not formalized:**
  * the compression form of expansion (step 1);
  * the CP rules as an explicit inductive system (only their soundness and premise count are used, through `SD`).
* **Open:** W_CP, and with it the target.
* **Next edge, if W_CP stays stuck:** Res(k) at k of order log n on random 3-CNF. There the lines are k-DNFs, and a
  restriction kills a term by fixing one of its literals, so a size-width-type step has a chance. The known bounds stop
  near sqrt(log n / log log n).

## 8. References

* V. Chvatal, E. Szemeredi, Many hard examples for resolution, J. ACM 1988.
* E. Ben-Sasson, A. Wigderson, Short proofs are narrow: resolution made simple, J. ACM 2001.
* E. Ben-Sasson, R. Impagliazzo, Random CNF's are hard for the polynomial calculus, FOCS 1999.
* M. Alekhnovich, A. Razborov, Lower bounds for polynomial calculus: non-binomial case, 2003.
* D. Grigoriev, Linear lower bound on degrees of Positivstellensatz calculus proofs for the parity, 2001.
  G. Schoenebeck, Linear level Lasserre lower bounds for certain k-CSPs, FOCS 2008.
* M. Alekhnovich, Lower bounds for k-DNF resolution on random 3-CNFs, STOC 2005; Computational Complexity 2011.
* P. Pudlak, Lower bounds for resolution and cutting plane proofs and monotone computations, JSL 1997.
* J. Buresh-Oppenheim, N. Galesi, S. Hoory, A. Magen, T. Pitassi, Rank bounds and integrality gaps for cutting planes
  procedures, FOCS 2003; Theory of Computing 2006.
* N. Fleming, D. Pankratov, T. Pitassi, R. Robere, Random Theta(log n)-CNFs are hard for cutting planes, FOCS 2017.
* P. Hrubes, P. Pudlak, Random formulas, monotone circuits, and interpolation, FOCS 2017.
* R. Impagliazzo, P. Pudlak, J. Sgall, Lower bounds for the polynomial calculus and the Groebner basis algorithm,
  Computational Complexity 1999.
* A. Urquhart, Hard examples for resolution, J. ACM 1987.
* D. Dadush, S. Tiwari, On the complexity of branching proofs, CCC 2020.
* D. Sokolov, Random (log n)-CNF are hard for cutting planes (again), STOC 2024 (ECCC TR23-086).
* A. Riazanov, A. Sofronova, D. Sokolov, W. Yuan, Searching for falsified clause in random (log n)-CNFs is hard for
  randomized communication, APPROX/RANDOM 2025.
* S. K. Bhattacharya, A. Chattopadhyay, Exponential lower bounds on the size of ResLin proofs of nearly quadratic depth,
  2025 (arXiv 2507.23008).
* `PROOF-SYSTEMS.md`, `DICHOTOMY-TRANSFER.md`, `NATIVE-METHOD.md` (this folder).
