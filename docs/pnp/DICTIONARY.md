# The gap-to-tractability dictionary

Private working note, 2026-11-23. It takes up the owner's entries on P vs NP in `../mass-gap/weak-coupling/PREP.md`
("A sane polynomial and P vs NP", "P and NP across and within a DB") and the owner's entry point of the same day:

> "Since inputs can be defined, there has to be an existence associated with them, if that existence is described by
> DMP-complete systems in its entirety, the DMP tools can be fully used."

The note builds a dictionary from the mass gap (decay of correlations in space) to tractability (fast sampling and
counting), proves its first two entries in Lean, states the rest as classical theorems with their exact hypotheses,
and then asks where the owner's entry leads: what it proves for a class of inputs, and what it would take to reach the
worst-case question P vs NP.

**Claim marks**

| Mark | Meaning |
|---|---|
| **[Lean]** | Proved in this repository, `docs/mass-gap/formal/ProofPhase/Mixing/` (Lean 4.34.0, Mathlib v4.34.0, standard axioms only; `axioms.sh`, `axioms.log`). Hypotheses listed with each theorem. |
| **[classical]** | A published theorem; reference in section 9. Not re-proved here. |
| **[conditional]** | A published theorem that holds under a complexity assumption, stated with it (here always NP != RP). |
| **[reading]** | An interpretation: a way of putting two results side by side. Not a theorem. |
| **[open]** | Not settled. |

---

## 0. The short answer

1. **Influence below 1 gives fast sampling.** If the Dobrushin influence sums of a finite system of n sites are at
   most alpha < 1, the single-site sampler (heat bath, Gibbs sampler) is within total-variation distance n alpha^t
   of equilibrium after t sweeps, from every start, so within epsilon after about log(n/epsilon)/log(1/alpha)
   sweeps: O(n log n) single-site updates. Random scan: the same order. **[Lean]**
2. **The spectral gap in time is the mass gap's theorem.** For a positive reversible Markov operator, time
   correlations decay at rate m exactly when the spectral measure has no mass above e^{-m}. It is the bridge's
   "decay rate = bottom of a positive spectral measure", applied as it stands after the change of variable
   E = -log(lambda). And influence below 1 gives a gap of at least (1 - alpha)/n per single-site step. **[Lean]**, with
   the spectral theorem for the Markov operator as a stated hypothesis (Mathlib lacks it).
3. **The chain to polynomial counting** (spatial mixing => uniform dynamical gap => polynomial sampling =>
   approximate counting) is classical, with exact hypotheses: finite range, bounded degree, closure under pinning.
   **[classical]**
4. **The converse beyond uniqueness**: for antiferromagnetic two-spin systems (hard-core gas, antiferromagnetic Ising),
   approximate counting is NP-hard just past the uniqueness threshold, unless NP = RP. **[conditional]** It does
   **not** hold for ferromagnets: the ferromagnetic Ising model loses uniqueness but stays approximately countable in
   polynomial time. Lattice gauge theory is on the ferromagnetic side. **[classical]**
5. **The owner's entry, formalized**: "inputs whose existence is described by DMP-complete systems" becomes a promise
   class of inputs that carry a local certificate (influence below 1 at a fixed scale with uniform constants; for
   constraint problems, the Lovasz local lemma condition). On the influence class: existence is guaranteed (decision is
   trivial), search, sampling and approximate counting are polynomial. On the local-lemma class: existence and search
   only; sampling and approximate counting need a strengthened regime (Moitra, degree below 2^{k/60}), and above about
   2^{k/2} approximate counting is NP-hard unless NP = RP (paper Part VI.1.8, VI.2.2). **[classical]**, assembled here
   (corrected 2026-11-24 after the part review R5). That is "P = NP
   within a DB" as a theorem about a class.
6. **It does not reach worst-case P vs NP by itself.** "Every input is in the class" is false for NP-complete problems
   (no-instances have no existence to certify), and the NP-hardness results beyond uniqueness say that extending the
   class to all inputs is equivalent to NP = RP. A proof that crosses from the class to all inputs must evade
   relativization and algebrization (either direction) and, for a separation, natural proofs. Section 6 checks each
   against the argument and names the one known route that evades all three. **[reading]**, on **[classical]**
   barrier theorems.

---

## 1. The dictionary

| Physics (the mass gap) | Algorithms (tractability) | Status |
|---|---|---|
| Configuration of a lattice system, Gibbs measure mu | Instance with its solution space; target distribution of a sampler | definitions |
| Influence (Dobrushin) column or row sum below 1 | One sweep contracts the coupling distance by alpha | **[Lean]** section 2 |
| Mass gap: correlations decay in space at rate m | Spatial mixing: far-away pinnings barely change local marginals | definitions |
| Transfer matrix e^{-H} >= 0 (reflection positivity) | Heat-bath Markov operator 0 <= P <= 1 (average of projections) | **[reading]** of two positivity facts |
| Spectral measure of H has no mass below m | Spectral measure of P has no mass above e^{-m} | **[Lean]** section 3, one theorem |
| Uniform gap in the volume | Mixing time O(n log n), uniform in the boundary condition | **[classical]** section 4 |
| Uniqueness of the infinite-volume state | Polynomial sampling and approximate counting | **[classical]** section 4 |
| Phase coexistence, non-uniqueness | Slow local dynamics; for antiferromagnets, NP-hard counting | **[classical]**, **[conditional]** section 5 |
| Domain boundary, surface tension | Barrier for local dynamics, exp(surface) crossing time; gadget site in hardness proofs | **[classical]** + **[reading]** section 7 |
| Local certificate at one scale (DMP-completeness, owner's term) | Promise class with a polynomial-time-checkable local condition | **[reading]** section 6 |

---

## 2. Lean part 1: influence below 1 gives fast mixing

File `ProofPhase/Mixing/Glauber.lean`. **[Lean]**

**Setting.** n sites, one measurable single-site space S (any: finite, a compact group, the reals) with a measurable
diagonal, an equilibrium probability measure mu on configurations. A `SiteDynamics mu` consists of:

* an update kernel P x for every site x that changes only the spin at x and leaves mu invariant (for the heat-bath
  update, invariance is the DLR equation at x);
* measurable couplings Q x of the updates from two configurations;
* an influence matrix A x z >= 0 (influence of z on x) with the **coupling form of Dobrushin's condition**: the coupled
  update at x disagrees at x with probability at most the sum of A x z over the sites z where the two configurations
  disagree.

For the heat-bath update, A x z is Dobrushin's coefficient (the largest total-variation distance between the
conditional laws at x for two boundary conditions differing only at z), and Q x glues maximal couplings along a chain
of hybrid boundary conditions. That construction is classical and is a **hypothesis** here, exactly as M1's (C) is a
hypothesis of `couplingDS_bound`.

**Results.**

| Theorem | Statement |
|---|---|
| `tv_sweep_le` | Systematic scan (any list containing every site), rows: if sum_z A x z <= alpha <= 1 for all x, then \|nu_t(s) - mu(s)\| <= n alpha^t after t sweeps, for every start nu and every measurable s. |
| `tv_rs_le` | Random scan, columns: if sum_x A x z <= alpha for all z, then \|nu_k(s) - mu(s)\| <= n (1 - (1 - alpha)/n)^k <= n e^{-(1 - alpha) k/n} after k single-site steps. |
| `mixing_sweep` | Distance <= epsilon once t log(1/alpha) >= log(n/epsilon): O(log n) sweeps. |
| `mixing_rs` | Distance <= epsilon once (1 - alpha) k >= n log(n/epsilon): O(n log n) updates. |
| `integral_sweep_le`, `integral_rs_le` | The same for bounded test functions, \|E_t F - E_mu F\| <= 2 M n alpha^t (resp. the random-scan rate). |

**How.** Run two copies of the sampler, one from nu and one from mu, with the same site choices, coupled by Q. Let
d(z) be the probability that the copies disagree at z. Updating x leaves d(z) unchanged for z != x and makes
d(x) <= sum_z A x z d(z). For systematic scan with row sums <= alpha, the largest d drops by the factor alpha per sweep
(a Gauss-Seidel argument: every value written during the sweep is at most alpha times the old maximum). For random
scan with column sums <= alpha, the total sum of d drops by the factor 1 - (1 - alpha)/n per step. The second copy
stays at mu (invariance), the first is the sampler's law, and the coupling inequality turns the total disagreement into
a total-variation bound.

**Reused from M1** (`ProofPhase.OneBox.CouplingDS`, imported, not edited): the disagreement events, their
measurability, the functional Phi, and `abs_integral_sub_le_phi`. The random-scan step is M1's averaged update T with
one-site blocks, no source blocks and coverage 1, so `phi_rsStepC_le` is `phi_T_le` with gamma = alpha and s = 0.
**New:** M1's theorem compares two invariant measures (both marginals fixed). Here the first marginal moves: the
coupled chain starts at nu x mu and its first marginal is the law of the sampler at time t. Also new: the per-site
estimates without support hypotheses, the max-norm contraction of a whole sweep, the total-variation bounds, and the
mixing times.

**Choices, stated.** Hypotheses on the kernels are asked at every configuration (no supports). This covers every
system with positive weights, so all of lattice gauge theory and soft-constraint spin systems; hard constraints
(proper colourings, independent sets) need M1's support sets, a routine extension. The systematic-scan theorem uses
row sums (Dobrushin's original condition), the random-scan theorem column sums (M1's column condition). Systematic scan
under column sums also mixes in O(log n) sweeps (Dyer-Goldberg-Jerrum 2008 treat such norm conditions; a weighted-norm
version of the argument above gives n alpha^t/(1 - alpha)) but is not formalized here. For a symmetric influence matrix the two conditions coincide.

---

## 3. Lean part 2: the spectral gap in time

File `ProofPhase/Mixing/TimeGap.lean`, link in `ProofPhase/Mixing/Link.lean`. **[Lean]**

**Setting.** P is a reversible Markov operator on L^2(mu) with 0 <= P <= 1. The random-scan heat-bath operator is
one: each single-site heat-bath update is the conditional expectation given the other spins, an orthogonal projection,
and the random-scan operator is their average. Lazy chains (1 + P')/2 are another. For f of mean zero the spectral
theorem gives a finite measure rho on [0, 1] with <f, P^k f> = integral of lambda^k d rho(lambda). **Hypothesis:**
rho is given with this property (Mathlib has no spectral theorem for self-adjoint operators; the bridge makes the
same assumption on the Yang-Mills side).

**Results.**

| Theorem | Statement |
|---|---|
| `time_gap_iff` | (exists K, for all k: integral lambda^k d rho <= K e^{-m k}) iff rho(lambda > e^{-m}) = 0. |
| `gap_of_geometric`, `geometric_of_gap` | Correlations <= K theta^k for all k iff no spectral mass above theta (theta > 0). |
| `spectral_gap_of_column` | Column sums of the influence matrix <= alpha in (0, 1), F bounded: the spectral measure of F for the random-scan operator has no mass above 1 - (1 - alpha)/n. |

**How.** Substitute E = -log(lambda). Then lambda^k = e^{-k E}, and the part of rho on lambda > 0 becomes a positive
measure on [0, inf) (`rateMeasure`); the atom at lambda = 0 only affects k = 0 and is absorbed in K. Now the bridge's
`spectral_gap_iff_nat` (imported, not edited) applies verbatim. In the link, the decay |C_F(k)| <= 2 M^2 n theta^k
comes from `integral_rs_le` started at a point mass, uniformly in the starting point, so no measurability of
x -> (R^k F)(x) is needed; `gap_of_geometric` then gives the gap.

**Reading.** **[reading]** The mass gap and the spectral gap of a sampler are one theorem about positive spectral
measures, read in two times: Euclidean time (transfer matrix e^{-H}, positive by reflection positivity, decay rate =
bottom of the spectrum of H) and algorithmic time (heat-bath operator, positive because it averages projections,
relaxation rate = bottom of the spectrum of -log P). The positivity that builds the Hilbert space on the physics side
is the positivity that makes the sampler's correlations a Laplace transform. Continuous-time Glauber dynamics
(generator L >= 0) needs no new statement: there <f, e^{-tL} f> is the bridge's `corr` and `spectral_gap_iff` is the
theorem.

---

## 4. The chain: spatial mixing => uniform dynamical gap => polynomial sampling and counting

**Step A, spatial mixing => dynamical gap uniformly in the volume.** **[classical]**

* *Dobrushin's condition* (row or column influence sum < 1) gives uniqueness of the Gibbs state (Dobrushin 1968) and
  fast mixing (section 2; Aldous, Bubley-Dyer, and the Lean statement here).
* *Stroock-Zegarlinski (1992).* For a finite-range, translation-invariant interaction on Z^d with finite single-spin
  space, the Dobrushin-Shlosman complete analyticity condition (strong mixing for all finite volumes) is equivalent to
  a logarithmic Sobolev inequality for the heat-bath (Glauber) dynamics with a constant uniform in the volume and the
  boundary condition.
* *Martinelli-Olivieri (1994).* Same class of interactions (they treat finite single-spin spaces): strong mixing on
  the volumes that are unions of cubes of a fixed side (exponential decay, uniform in the boundary condition, of the
  effect of a boundary change on local observables) implies a spectral gap and a log-Sobolev constant of the Glauber
  dynamics bounded away from zero uniformly in all such volumes and all boundary conditions. In d = 2 weak mixing
  suffices for squares (Martinelli-Olivieri-Schonmann 1994).
* A uniform log-Sobolev constant gives continuous-time mixing in time O(log |Lambda|), so O(n log n) single-site
  updates for n = |Lambda|. A uniform gap alone gives O(n^2) updates for discrete chains.

**Step B, polynomial sampling => approximate counting.** **[classical]**

* *Jerrum-Valiant-Vazirani (1986).* For a self-reducible problem, an almost-uniform sampler running in polynomial time
  gives a fully polynomial randomized approximation scheme (FPRAS) for the count, and conversely. For a spin system
  "self-reducible" means: pinning one spin gives a system of the same class. The partition function is written as a
  telescoping product of ratios Z(pinned_i)/Z(pinned_{i-1}), each a marginal probability estimated by sampling.
* The precise requirement is that the sampler works **for every pinned instance**. This is exactly why uniformity in
  the boundary condition (Step A) matters, and why Dobrushin's condition is so well suited: Dobrushin coefficients are
  suprema over boundary conditions, so pinning sites never increases them. The class "influence sums <= alpha" is
  closed under pinning.
* Jerrum-Sinclair (1989, 1993): FPRAS for the monomer-dimer system and for the ferromagnetic Ising model at all
  temperatures; Jerrum-Sinclair-Vigoda (2004): the permanent of non-negative matrices.

**Step B', correlation decay => deterministic counting.** **[classical]**

* *Weitz (2006).* For the hard-core model on graphs of maximum degree D and fugacity lambda < lambda_c(D) =
  (D - 1)^{D-1}/(D - 2)^D (the uniqueness threshold of the infinite D-regular tree), a deterministic algorithm
  approximates the partition function within a factor 1 +/- epsilon in time polynomial in n/epsilon for fixed D. The
  ingredient is strong spatial mixing on the tree of self-avoiding walks: correlation decay itself is the algorithm,
  no Markov chain.
* *Anari-Liu-Oveis Gharan (2020), Chen-Liu-Vigoda (2021).* For the same range lambda < lambda_c(D), Glauber dynamics
  mixes in O(n log n) steps on every graph of maximum degree D (spectral independence). So for the hard-core model the
  whole chain is now proved up to the threshold: uniqueness on the tree => fast local dynamics on all bounded-degree
  graphs => FPRAS.

**Summary of the chain.** For bounded-degree, finite-range systems with uniform constants:
gap in space (strong spatial mixing) => gap in time, uniform in volume and boundary => sampling in O(n log n) =>
approximate counting in polynomial time. Every arrow is a theorem with the hypotheses named above. **[classical]**

---

## 5. The converse beyond uniqueness

**[conditional]**, assumption NP != RP. RP is randomized polynomial time with one-sided error; NP != RP is widely
believed and implies P != NP.

* *Sly (2010).* For every D >= 6 there is epsilon(D) > 0 such that for lambda_c(D) < lambda < lambda_c(D) + epsilon(D)
  there is no FPRAS for the hard-core partition function on graphs of maximum degree D, unless NP = RP.
* *Sly-Sun (2014); Galanis-Stefankovic-Vigoda (2016).* For every D >= 3 and every lambda > lambda_c(D), and for the
  antiferromagnetic Ising model throughout its non-uniqueness region on D-regular graphs: no FPRAS unless NP = RP.
  Galanis-Stefankovic-Vigoda (2015) extend this to antiferromagnetic multi-spin systems (colourings, antiferromagnetic
  Potts) in the tree non-uniqueness region.
* **How the hardness is built.** The reduction is from MAX-CUT. The gadget is a random bipartite D-regular graph, which
  beyond uniqueness has two phases (one side of the bipartition occupied, or the other). Each gadget stores one bit as
  its phase; the edges between gadgets count the cut through the interfaces between phases. An approximate counter
  would read off the maximum cut. The non-uniqueness, the coexistence of two phases, is the computing element.

So for antiferromagnetic two-spin systems the computational transition sits exactly at the physical one: below the
uniqueness threshold everything is polynomial (section 4), above it approximate counting is NP-hard. **[classical]** +
**[conditional]**

**The exception that matters here: ferromagnets.** **[classical]** The ferromagnetic Ising model loses uniqueness below
the critical temperature, Glauber dynamics on the torus then needs time exponential in the surface L^{d-1} to cross
between the two phases (Thomas 1989; Borgs-Chayes-Frieze-Kim-Tetali-Vigoda-Vu 1999), yet the partition function has an
FPRAS at every temperature (Jerrum-Sinclair 1993, through the even-subgraph representation). Loss of uniqueness slows
local dynamics; it does not make counting hard when a global positive representation exists. (Ferromagnetic Potts with
q >= 3 sits in between: hard for the intermediate class #BIS in general (Goldberg-Jerrum 2012) and on bounded-degree
graphs beyond its order-disorder transition (Galanis-Stefankovic-Vigoda-Yang 2016), not known to be NP-hard.) Lattice gauge theory with the Wilson action is on this side: positive weights, reflection
positivity, a random-surface representation in the strong-coupling regime. The dictionary therefore predicts slow
local dynamics at phase boundaries for gauge theories (critical slowing down as the column approaches 1, topological
freezing between topological sectors at fine lattice spacing) but no NP-hardness from phase coexistence. **[reading]**

---

## 6. The owner's entry: inputs whose existence is described by DMP-complete systems

### 6.1 Three ways to make it precise

The entry says: an input exists, so an "existence" is attached to it; if that existence is fully described by a
DMP-complete system, the DMP tools apply. In the PREP readings "DMP-complete" was read as "can always be certified
locally". There are three standard ways to turn "inputs of a certain kind" into mathematics.

1. **A promise class.** Fix constants alpha < 1, a scale L and a degree bound D. The class Pi(alpha, L, D) consists of
   the instances (a bounded-degree spin system or constraint system) whose influence matrix, after blocking at scale L,
   has column sums <= alpha. Its local twin for constraint problems is the Lovasz local lemma (LLL) class: each bad
   event has probability p, depends on at most d others, and e p (d + 1) <= 1.
2. **A restricted language.** The same class, with membership checked by the algorithm. For bounded degree and finite
   spins this is possible in polynomial time: each Dobrushin coefficient is a supremum over the finitely many
   configurations of a bounded neighbourhood. The LLL condition is read off the formula. **[classical]**
3. **A distribution on inputs.** Inputs drawn from a law under which, with high probability, the instance lies in the
   class (random sparse instances well below their thresholds). This is average-case complexity and says nothing about
   worst-case P vs NP.

The first two are the right formalization of "existence described in its entirety": every input considered carries
the local certificate, and the certificate is itself checkable.

### 6.2 What the dictionary proves for that class

**[classical]**, assembled; the mixing step **[Lean]**.

* **Decision is trivial: existence is guaranteed.** In the LLL class every instance has a solution (Lovasz local
  lemma, 1975). In the Dobrushin class the Gibbs measure exists and is unique, so the solution space is non-empty and
  has one phase. This is the formal content of "there has to be an existence associated with them": the local
  certificate is a proof of existence.
* **Search is polynomial.** Moser-Tardos (2010): in the LLL class a satisfying assignment is found in expected
  polynomial time by resampling violated constraints, a local dynamics. In the Dobrushin class the sampler of
  section 2 produces a typical configuration.
* **Sampling is polynomial.** Section 2 (Dobrushin class: O(n log n) updates). For bounded-degree k-CNF formulas in a
  strengthened LLL regime, Moitra (2017) gave approximate counting and sampling of solutions, for variable degree below
  2^{k/60}; later work enlarged the exponent.
* **Approximate counting is polynomial.** Section 4, Step B: the Dobrushin class is closed under pinning, so
  Jerrum-Valiant-Vazirani applies.
* **The boundary of the class is a computational transition.** For k-CNF formulas, approximate counting becomes
  NP-hard (unless NP = RP) once the variable degree exceeds a constant times 2^{k/2} (Bezakova, Galanis, Goldberg,
  Guo, Stefankovic 2019); for the hard-core model the transition is exactly lambda_c(D) (sections 4, 5).

In one line: **on inputs whose existence is certified locally, existence costs nothing to decide, and finding,
sampling and approximately counting cost polynomial time.** That is "P = NP within a DB" as a theorem about a class.
Strictly it is stronger than P = NP on the class (approximate counting is in general harder than NP decision), and
weaker in another way: the decision problem on the class is trivial, so the class contains no hard NP decisions to
begin with.

### 6.3 What it would take to reach worst-case P vs NP

P vs NP is about **every** input of an NP-complete problem. Two routes lead from the class to all inputs.

* **Collapse (P = NP): every input reduces to the class.** A polynomial map sending every SAT instance to an
  equivalent instance with a local certificate. This is impossible for the LLL class as it stands: its instances are
  all satisfiable, so the map would itself have to decide satisfiability. For the counting version the hardness
  results of section 5 say: putting all instances inside uniqueness is equivalent to NP = RP. So "the existence of
  every input is described by a DMP-complete system" is not a weaker hypothesis that implies P = NP; for counting it is
  as strong as NP = RP, and for decision it fails on the no-instances, which have no existence to describe. **[classical]**
  (the reductions) + **[reading]** (the conclusion).
* **Separation (P != NP): the inputs outside the class are hard.** "Hardness lives at the boundary" would have to be
  proved unconditionally. The known boundary-hardness theorems (section 5) assume NP != RP, so they move the question,
  they do not answer it.

**The three barriers, checked against the argument.** **[reading]** on **[classical]** barrier theorems.

| Barrier | What it says | Applies to the dictionary? | What a proof would need |
|---|---|---|---|
| Relativization (Baker-Gill-Solovay 1975) | There are oracles A, B with P^A = NP^A and P^B != NP^B, so a proof that works equally with any oracle cannot settle P vs NP. | **Yes, in both directions.** The coupling proof of section 2 treats the update rule as a black box (it uses only locality, invariance and the influence bound); an oracle can be added to every machine and the proof goes through. The hardness reductions of section 5 are gadget constructions, which also relativize. | An ingredient that looks inside the computation: arithmetization of the verifier (as in IP = PSPACE), or a locality property of computations themselves rather than of the instances. |
| Natural proofs (Razborov-Rudich 1997) | A lower-bound proof that uses a property of Boolean functions that is constructive (decidable in time polynomial in the truth table, 2^n) and large (true for a non-negligible fraction of all functions) would break pseudorandom functions, which exist if one-way functions exist. | **Only to the separation direction.** "This function's associated Gibbs system is beyond uniqueness" is constructive (influences are computable from the truth table in time polynomial in 2^n) and very likely large (random functions are maximally non-local). Used as a lower-bound property it would be natural. | A non-large property tied to the structure of the specific hard function (e.g. its symmetries or self-reducibility), or a non-constructive one. The upper-bound (collapse) direction is not affected. |
| Algebrization (Aaronson-Wigderson 2009) | Extends relativization to oracles with low-degree algebraic extensions; covers arithmetization-based proofs. Settling P vs NP needs non-algebrizing techniques. | **Yes, in both directions.** The algebraic tools of the dictionary (partition functions as polynomials, zero-free regions and Barvinok-Patel-Regts interpolation, which give the same FPTAS range as correlation decay) algebrize. | Techniques that neither relativize nor algebrize. |

**The one known route that evades all three.** Williams (2014) proved that a satisfiability algorithm for a circuit
class C that beats brute force (2^n / n^{omega(1)}) implies NEXP is not contained in C, and gave such an algorithm for
ACC^0 circuits; the resulting lower bound is neither relativizing, natural nor algebrizing. This is where a tractability
dictionary can turn into a lower bound: **if** local certification gave a faster-than-brute-force satisfiability
algorithm for some circuit class (a "locality" speed-up on the satisfiability of circuits, not on Gibbs instances),
Williams's theorem would convert it into a circuit lower bound for NEXP. That is far weaker than P != NP, but it is the
one known mechanism by which "algorithms inside" become "hardness outside". **[open]**: no such speed-up from the
dictionary is known.

**Where the entry leads, exactly.** It leads to a theorem about a class (6.2), which is proved. It does not lead to
worst-case P vs NP by itself: the crossing from the class to all inputs is either impossible as stated (collapse for
decision), equivalent to NP = RP (collapse for counting), or a separation that must evade all three barriers.
Of the barriers the one the DMP reading runs into first is **natural proofs**: "boundary-rich functions are hard" is
the shape of a large, constructive property. To evade it the hardness property must be specific to the hard function
(non-large), which in DMP terms means: the boundary must be a feature of one particular existence, not of a typical
one. **[reading]**

---

## 7. DMP reading (separate, marked)

This section states the owner's DMP entries in the language of the dictionary. Everything here is **[reading]**
unless marked otherwise; the theorems it leans on are in sections 2 to 6.

* **"P = NP within a DB."** Within one phase (one side of a domain boundary: correlations decay, the equilibrium is
  unique, the column is below 1 at some scale), finding, sampling and approximately counting cost no more than
  checking, up to polynomial factors. Theorem form: section 6.2. The DMP word for the certificate is
  "DMP-complete: certified locally"; the theorem's word is "influence below 1", and its consequence in algorithmic
  time is the spectral gap of section 3, the same statement as the mass gap.
* **"P != NP across a DB."** Crossing a boundary costs: local dynamics need time exponential in the boundary's area
  (surface tension is the barrier; **[classical]**, Thomas; Borgs et al.), and beyond uniqueness approximate counting
  of antiferromagnets is NP-hard (**[conditional]**, Sly; Sly-Sun; Galanis-Stefankovic-Vigoda). As a statement about
  the classes P and NP it is not proved; it is the separation route of 6.3 and meets all three barriers.
* **"Hardness lives at the boundaries."** The hardness proofs of section 5 make this literal: the gadgets are phase
  boundaries, one bit per phase, and the cut is counted across the interfaces. Random constraint problems show the
  same split, hard where the solution space shatters into clusters separated by barriers (Mezard-Parisi-Zecchina 2002;
  Achlioptas-Coja-Oghlan 2008). In the proof the boundary's cost is the twist free energy (Flip/Strict, Z_tw < Z) and
  the area law says how much.
* **The ferromagnetic exception in DMP terms.** A boundary that can be certified globally (one positive
  representation for the whole system, as the even-subgraph or random-cluster expansion for ferromagnets) slows local
  dynamics but does not make counting hard. Yang-Mills is of this kind (reflection positivity is a global positivity),
  so for the gauge theory the DMP reading predicts **cost at the boundary in Monte Carlo time** (critical slowing
  down, topological freezing) rather than computational hardness.
* **The project's central quantity read twice.** Getting the column below 1 at some scale is both the physical
  condition (the gap propagates, M1) and the computational one (the system is polynomially samplable and countable
  from that scale on, sections 2 to 4). The IR session's value 1.02 at L sqrt(sigma) = 2.80 is just above 1, so neither
  reading is certified at that scale yet.

---

## 8. What is proved, what is conditional, what is missing

**Proved in Lean** (65 declarations, standard axioms only, `axioms.log`):
* fast mixing from influence below 1, systematic scan (rows) and random scan (columns), with total-variation and
  test-function bounds and explicit mixing times (`Glauber.lean`);
* the spectral gap in time as the bridge's decay-rate theorem (`TimeGap.lean`);
* influence below 1 => spectral gap >= (1 - alpha)/n of the random-scan sampler (`Link.lean`).

**Hypotheses of the Lean statements** (not proved here): the coupling form of Dobrushin's condition (existence of the
measurable couplings Q, as M1's (C)); the spectral theorem for the Markov operator (`hrep`) and its positivity
(spectral measure on [0, 1]).

**Classical, not formalized:** Stroock-Zegarlinski, Martinelli-Olivieri (spatial => uniform dynamical gap);
Jerrum-Valiant-Vazirani (sampling <=> counting); Weitz; Anari-Liu-Oveis Gharan, Chen-Liu-Vigoda; Moser-Tardos;
Moitra; the barrier theorems. Mathlib has Turing machines and polynomial-time computability but no classes NP or RP
and no approximate-counting framework, so the complexity statements cannot yet be stated in Lean without building
that layer.

**Conditional:** the NP-hardness of approximate counting beyond uniqueness (Sly; Sly-Sun; Galanis-Stefankovic-Vigoda;
Bezakova et al.), all under NP != RP.

**Missing, in order of size:**
1. *Lean, small:* the construction of Q from classical Dobrushin coefficients for finite S (maximal couplings glued
   along hybrids); systematic scan under column sums; support sets for hard constraints.
2. *Lean, medium:* positivity of the heat-bath operator (average of conditional expectations) and the spectral
   measure for finite S (finite-dimensional spectral theorem is in Mathlib), which would remove `hrep` for finite
   systems.
3. *Physics:* the column below 1 at a certified scale for the gauge theory (currently 1.02 at the measured scale).
4. *Complexity, open:* any route from the class theorem to all inputs. Collapse is ruled out for decision and is
   equivalent to NP = RP for counting; separation must evade relativization, natural proofs and algebrization, and the
   one known evading mechanism (Williams) would need a faster-than-brute-force circuit-satisfiability algorithm from
   locality, which nothing here provides.

---

## 9. References

* Dobrushin, R. L. (1968, 1970). The description of a random field by means of conditional probabilities; Prescribing
  a system of random variables by conditional distributions. Theory Probab. Appl.
* Dobrushin, R. L., Shlosman, S. B. (1985, 1987). Completely analytical interactions.
* Stroock, D. W., Zegarlinski, B. (1992). The equivalence of the logarithmic Sobolev inequality and the
  Dobrushin-Shlosman mixing condition, Comm. Math. Phys. 144; The logarithmic Sobolev inequality for discrete spin
  systems on a lattice, Comm. Math. Phys. 149.
* Martinelli, F., Olivieri, E. (1994). Approach to equilibrium of Glauber dynamics in the one phase region I, II.
  Comm. Math. Phys. 161.
* Martinelli, F., Olivieri, E., Schonmann, R. H. (1994). For 2-D lattice spin systems weak mixing implies strong
  mixing. Comm. Math. Phys. 165.
* Dyer, M., Goldberg, L. A., Jerrum, M. (2008). Dobrushin conditions and systematic scan. Combin. Probab. Comput. 17.
* Jerrum, M., Valiant, L., Vazirani, V. (1986). Random generation of combinatorial structures from a uniform
  distribution. Theoret. Comput. Sci. 43.
* Jerrum, M., Sinclair, A. (1989, 1993). Approximating the permanent; Polynomial-time approximation algorithms for the
  Ising model. SIAM J. Comput.
* Jerrum, M., Sinclair, A., Vigoda, E. (2004). A polynomial-time approximation algorithm for the permanent of a matrix
  with non-negative entries. J. ACM 51.
* Weitz, D. (2006). Counting independent sets up to the tree threshold. STOC.
* Anari, N., Liu, K., Oveis Gharan, S. (2020). Spectral independence in high-dimensional expanders and applications to
  the hardcore model. FOCS.
* Chen, Z., Liu, K., Vigoda, E. (2021). Optimal mixing of Glauber dynamics: entropy factorization via high-dimensional
  expansion. STOC.
* Sly, A. (2010). Computational transition at the uniqueness threshold. FOCS.
* Sly, A., Sun, N. (2014). Counting in two-spin models on d-regular graphs. Ann. Probab. 42.
* Galanis, A., Stefankovic, D., Vigoda, E. (2015, 2016). Inapproximability for antiferromagnetic spin systems in the
  tree non-uniqueness region, J. ACM 62; Inapproximability of the partition function for the antiferromagnetic Ising
  and hard-core models, Combin. Probab. Comput. 25.
* Goldberg, L. A., Jerrum, M. (2012). Approximating the partition function of the ferromagnetic Potts model. J. ACM 59.
* Galanis, A., Stefankovic, D., Vigoda, E., Yang, L. (2016). Ferromagnetic Potts model: refined #BIS-hardness and
  related results. SIAM J. Comput. 45.
* Thomas, L. E. (1989). Bound on the mass gap for finite volume stochastic Ising models at low temperature. Comm. Math.
  Phys. 126.
* Borgs, C., Chayes, J., Frieze, A., Kim, J. H., Tetali, P., Vigoda, E., Vu, V. (1999). Torpid mixing of some Monte
  Carlo Markov chain algorithms in statistical physics. FOCS.
* Erdos, P., Lovasz, L. (1975). Problems and results on 3-chromatic hypergraphs (the local lemma).
* Moser, R. A., Tardos, G. (2010). A constructive proof of the general Lovasz local lemma. J. ACM 57.
* Moitra, A. (2019). Approximate counting, the Lovasz local lemma, and inference in graphical models. J. ACM 66.
* Bezakova, I., Galanis, A., Goldberg, L. A., Guo, H., Stefankovic, D. (2019). Approximation via correlation decay when
  strong spatial mixing fails. SIAM J. Comput. 48.
* Mezard, M., Parisi, G., Zecchina, R. (2002). Analytic and algorithmic solution of random satisfiability problems.
  Science 297.
* Achlioptas, D., Coja-Oghlan, A. (2008). Algorithmic barriers from phase transitions. FOCS.
* Baker, T., Gill, J., Solovay, R. (1975). Relativizations of the P =? NP question. SIAM J. Comput. 4.
* Razborov, A., Rudich, S. (1997). Natural proofs. J. Comput. System Sci. 55.
* Aaronson, S., Wigderson, A. (2009). Algebrization: a new barrier in complexity theory. ACM Trans. Comput. Theory 1.
* Williams, R. (2014). Nonuniform ACC circuit lower bounds. J. ACM 61.
* Barvinok, A. (2016). Combinatorics and Complexity of Partition Functions. Springer. Patel, V., Regts, G. (2017).
  Deterministic polynomial-time approximation algorithms for partition functions and graph polynomials. SIAM J.
  Comput. 46.
