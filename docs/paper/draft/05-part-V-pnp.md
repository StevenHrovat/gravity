# Part V. P vs NP: inside a certified class, and across it

*Draft 2, 2026-11-23. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/ProofPhase/`; notes relative to
`docs/pnp/`. Claim labels (V.n) are listed in `../CLAIMS.md`.*

## V.0 What is proved and what is not

**This part does not resolve P vs NP, nor NP vs coNP.** It proves, in Lean, the sampling side of the chain of II.0 for finite systems
(V.1) and the exact parts of the dichotomy for refutations (V.3). It then takes the strongest proof system in which the structureless
case is open, cutting planes on random 3-CNF, and locates the open step there to one missing cost measure (V.4, V.5). Every closing
argument must pass the relativization, natural-proofs and algebrization barriers (V.7).

Two notions of the problem are used:

* **P vs NP** (decision, search, counting): `DICTIONARY.md`.
* **NP vs coNP** via proof systems: a polynomially bounded proof system exists iff NP = coNP **[classical]** (Cook-Reckhow 1979);
  NP != coNP implies P != NP. `PROOF-SYSTEMS.md`. The owner's title names NP vs coNP for this reason: the proof-complexity side is
  where this part's work sits.

## V.1 Inside a certified class: the chain holds (links 1 to 4)

A finite spin system with positive weights whose Dobrushin influences sum to less than one is easy in every sense: its sampler mixes
fast, its dynamics has a spectral gap, and through self-reducibility counting and search follow. All the finite pieces are now
unconditional in Lean: the couplings that earlier files assumed are built from the classical objects, and the spectral measure is
proved from Mathlib's finite-dimensional spectral theorem (`ITEMS.md`).

| # | Result | Status | Source |
|---|---|---|---|
| V.1.1 | Dobrushin row sums at most alpha < 1 (finite system, positive weights): the heat-bath sampler is within n alpha^t of equilibrium after t sweeps; random scan under column sums | **[Lean]** | `Mixing/Classical.lean`, `tv_sweep_dobrushin`, `tv_rs_dobrushin`, `mixing_sweep_dobrushin` |
| V.1.2 | The column condition gives a spectral gap of at least (1 - alpha)/n per single-site step; the spectral measure exists and lies in [0, 1] | **[Lean]** | `Mixing/FiniteSpectral.lean`, `spectral_gap_dobrushin`, `timeCorr_spectral`, `exists_spectral_measure` |
| V.1.3 | Gap in time iff no spectral mass above e^{-m} | **[Lean]** | `Mixing/TimeGap.lean`, `time_gap_iff` |
| V.1.4 | Doeblin contraction, sharpness, eta^n along a homogeneous chain, the box bound under a density floor | **[Lean]** | `Mixing/Doeblin.lean`, `contracts_of_doeblin`, `doeblin_sharp`; `Mixing/Chain.lean`, `contracts_kpow`, `box_bound` |
| V.1.5 | Dobrushin condition gives a unique Gibbs state; spatial mixing gives a volume-uniform gap | **[classical]** | Dobrushin 1968, 1970; Stroock-Zegarlinski 1992; Martinelli-Olivieri 1994 |
| V.1.6 | Polynomial sampling gives polynomial approximate counting for self-reducible problems, and back | **[classical]** | Jerrum-Valiant-Vazirani 1986 |
| V.1.7 | Hard-core model below lambda_c(D): deterministic counting (correlation decay) and O(n log n) mixing | **[classical]** | Weitz 2006; Anari-Liu-Oveis Gharan 2020; Chen-Liu-Vigoda 2021 |
| V.1.8 | **The certified class** (influence sums below alpha after blocking, or the Lovasz local lemma condition): existence guaranteed, search, sampling and approximate counting polynomial | **[classical]** assembled; mixing step **[Lean]** | `DICTIONARY.md`, 6.2; Lovasz 1975; Moser-Tardos 2010; Moitra 2019 |
| V.1.9 | Not yet unconditional: infinite or continuous single-site spaces (the gauge group), hard constraints, systematic scan under column sums | **[open]** in Lean; **[classical]** on paper | `ITEMS.md`, 3 |

The finite results are the same theorems Part III uses for Yang-Mills (II.4); the gauge-theory instance still rests on the couplings
and the L^2 spectral theorem as hypotheses (V.1.9).

## V.2 At the edge of the class: what is known to go wrong

| # | Result | Status | Source |
|---|---|---|---|
| V.2.1 | Antiferromagnetic two-spin systems beyond uniqueness: no FPRAS unless NP = RP | **conditional** (NP != RP) | Sly 2010; Sly-Sun 2014; Galanis-Stefankovic-Vigoda 2015, 2016 |
| V.2.2 | Bounded-degree k-CNF: approximate counting NP-hard above degree c 2^{k/2} | **conditional** | Bezakova-Galanis-Goldberg-Guo-Stefankovic 2019 |
| V.2.3 | The ferromagnetic Ising model loses uniqueness but keeps an FPRAS at every temperature | **[classical]** | Jerrum-Sinclair 1993 |
| V.2.4 | Lattice gauge theory with the Wilson action is on the ferromagnetic side: slow dynamics at phase boundaries, but no NP-hardness from coexistence is predicted | **[reading]** | `DICTIONARY.md`, 5 |
| V.2.5 | Putting all counting instances inside the uniqueness region is as strong as NP = RP; reducing SAT into the LLL class is impossible as stated (all LLL instances are satisfiable) | **conditional** / **[classical]** | `DICTIONARY.md`, 6.3 |

## V.3 Refutations: the dichotomy transferred (NP vs coNP)

A refutation proves that a formula has no satisfying assignment: the remnant "it does not exist". Resolution always finds one, and
every refutation in every sound two-premise system must, somewhere, cross from local facts to a global one. That crossing is
universal; its cost is not.

**Confinement times resolution (the size-width relation).** In resolution the cost of the crossing has two terms: the width the
crossing must assert (confinement: the cut principle, width at least the boundary), and the share of it one restriction resolves
(resolution). The DAG-like size-width relation is now in Lean: if width w + d + b is impossible, every DAG-like refutation has size at
least exp(b (w + d + 1)/2n) **[Lean]** (`Proof/Dag.lean`, `size_width`, `size_width_exp`). With the cut principle the same bound
holds whenever w + d + b < e, e the boundary of every middle region **[Lean]** (`dag_size_ge`); optimising b gives
exp((e - w)^2 / 8n) up to rounding **[paper]**. This is Ben-Sasson-Wigderson (2001) **[classical]**, now machine-checked.

| # | Result | Status | Source |
|---|---|---|---|
| V.3.1 | Resolution is sound and refutation-complete: refutable iff unsatisfiable | **[Lean]** | `Proof/Resolution.lean`; `Proof/Complete.lean`, `refutable_iff` |
| V.3.2 | No inference creates assertion; every refutation has a middle-sized clause; resolution width is at least the boundary count | **[Lean]** | `Proof/Cut.lean`, `exists_middle`, `width_ge` |
| V.3.3 | Tree-like size-width: width W forces more than 2^{W - w} leaves | **[Lean]** | `Proof/SizeWidth.lean`, `tl_size_gt` |
| V.3.4 | DAG-like size-width: size >= exp(b (w + d + 1)/2n); with the cut principle for w + d + b < e, hence exp((e - w)^2 / 8n) | **[Lean]** (the optimisation over b **[paper]**; classical: Ben-Sasson-Wigderson 2001) | `Proof/Dag.lean`, `size_width`, `size_width_exp`, `dag_size_ge` |
| V.3.5 | Tseitin on expanders: resolution width at least the expansion, with two stated hypotheses (sub-systems satisfiable; expansion count) | **[Lean]** with hypotheses | `Proof/Tseitin.lean`, `width_ge`, `tl_size_ge` |
| V.3.6 | Gauss law mod 2: boundary parity equals interior charge; odd charge is unsatisfiable | **[Lean]** | `Proof/Crossing.lean`, `gauss`, `unsat_of_odd` |
| V.3.7 | **Every refutation crosses:** in every sound system with at most two premises per rule, every refutation of an expanding formula has a line sensitive to at least the expansion many variables | **[Lean]** with the two hypotheses of V.3.5 | `Proof/Crossing.lean`, `cross_any_system` |
| V.3.8 | The crossing is universal, its cost is not: one XOR names the Tseitin flux; resolution pays 2^{b-1} clauses of width b for it, Frege about b^2 symbols | **[Lean]** (`summary`) / **[classical]** | `DICHOTOMY-TRANSFER.md`, 3 |
| V.3.9 | Known lower bounds: resolution (Haken 1985; Urquhart 1987; Chvatal-Szemeredi 1988), bounded-depth Frege (Ajtai 1988; Pitassi-Beame-Impagliazzo 1993; Krajicek-Pudlak-Woods 1995), cutting planes (Pudlak 1997) | **[classical]** | `PROOF-SYSTEMS.md`, 2 |
| V.3.10 | Feasible interpolation for resolution and cutting planes; its failure for Frege and extended Frege under cryptographic assumptions | **[classical]** / **conditional** | Krajicek 1997; Pudlak 1997; Krajicek-Pudlak 1998; Bonet-Pitassi-Raz 2000 |
| V.3.11 | No superpolynomial lower bound is known for AC^0[p]-Frege, Frege or extended Frege; best formula lower bounds about n^3 | **[open]** / **[classical]** | Hastad 1998; Tal 2014 |

## V.4 The edge: cutting planes on random 3-CNF

**Why this system and this family.** Cutting planes (CP) is the strongest system in which random CNF is known to be hard only when the
clauses are wide enough: width Theta(log n) is solved, constant width is open **[classical]**. The other candidates are either solved
(polynomial calculus, sum-of-squares degree) or open for every formula, structured or not (Res(xor), bounded-depth Frege with parity
gates), so randomness is not their obstacle. The open part of CP is exactly the structureless, constant-width case **[classical]** +
**[reading]** for the choice (`EDGE.md`, 0.1).

**Target.** For a large constant Delta and a random 3-CNF F with Delta n clauses: with high probability every CP refutation of F has size
2^(n^Omega(1)) **[open]**.

**What closes.** (1) Incompressibility of the specific formula gives expansion: a small clause set spanning too few variables could be
described in fewer bits than its length. This is a statement about one input, not about typical Boolean functions, so the
natural-proofs barrier does not bite here **[classical]** (counting) + **[reading]** (the form). (2) Expansion forces the crossing in
CP: CP's rules are sound with at most two premises, so `cross_any_system` applies **[Lean]**.

**Where it stops.** In resolution the crossing line is a clause of width e, and any one literal kills it under a restriction, which
turns "sensitive to e variables" into size. In CP that step is false: the majority line "at least half of these e variables are true"
is sensitive to all e and survives every restriction of fewer than e/2 variables **[Lean]** (`Proof/Edge.lean`, `majority_line`,
`thr_sensitive`, `thr_survives`). The uncertainty term of the size-width relation collapses: one line can aggregate its units.

**The duality floor, and where it fails.** For a unit threshold "at least k of these e variables", forcing it true needs k fixed
variables and forcing it false needs e - k + 1; the two sum to e + 1, so every such line pays at least (e + 1)/2 in one channel **[Lean]**
(`Proof/CPDuality.lean`, `thr_duality`). This is the CP form of max(F_tw, F_e) >= c. It fails for weighted lines: the line
r x1 + r x2 + (sum of r further variables) >= 2r is sensitive to all r + 2 variables and is forced true by fixing two and false by
fixing two **[Lean]** (`two_cheap`). So no measure on single lines built from certificates gives the floor.

**Pairs, and the interface.** Feasible interpolation splits the formula as A(x, y) and B(x, z) and every line into an A-part and a
B-part sharing only x: two derived lines that share existence (x) and not possibility. The two boundary laws are disjoint exactly when
the formula is unsatisfiable **[Lean]** (`split_unsat_iff`). The cost is charged to the interface, a monotone real circuit (Pudlak 1997)
or a dag-like communication protocol **[classical]**. That passes clique-colouring and random k-CNF with k = Theta(log n) **[classical]**
(Hrubes-Pudlak; Fleming-Pankratov-Pitassi-Robere; Sokolov) and fails at constant width, where the interface carries O(1) bits per clause.
Every CP refutation of a 3-CNF contains a creative pair, a rounding of a combination of at least two lines, while rounding a single
axiom creates nothing; additive pairs cross for free **[Lean]** (`Proof/CPPairs.lean`, `creative_pair`, `round_single`, `fan_cheap`).
The pairwise form gives a floor in kind and in depth, not in size.

**Positivity runs to rank, not size.** The all-1/2 point satisfies every clause of width at least two and every sum of satisfied lines
**[Lean]** (`half_clause`); rounding breaks it **[Lean]** (`half_breaks_rounding`). Fractional points surviving r rounds give CP rank
lower bounds, known for random k-CNF (Buresh-Oppenheim et al.) **[classical]**, and rank bounds size only linearly. SOS-degree hardness
does not transfer to CP size: Tseitin needs linear SOS degree (Grigoriev 2001) but has quasi-polynomial CP refutations
(Dadush-Tiwari 2020) **[classical]**.

**The first unclosable step.** Both transfers stop at one place: **interface hardness at width 3**, a superpolynomial lower bound on
dag-like protocols for the falsified-clause search of a random 3-CNF under some balanced split. Equivalently, a cost measure W_CP on
CP lines that the crossing forces on every refutation of an expanding 3-CNF and that is expensive in size **[open]**. **No new lower
bound** is claimed.

| # | Result | Status | Source |
|---|---|---|---|
| V.4.1 | CP on random 3-CNF is the sharpest open case (log n width solved, constant width open) | **[classical]** + **[reading]** | `EDGE.md`, 0.1 |
| V.4.2 | Incompressibility of the one formula gives expansion; natural proofs do not bite | **[classical]** + **[reading]** | `EDGE.md`, 0.3 |
| V.4.3 | Expansion forces a crossing line in every CP refutation | **[Lean]** (hypotheses of V.3.5) | `Proof/Crossing.lean`, `cross_any_system` |
| V.4.4 | The majority line is sensitive to all e variables and survives restrictions of fewer than e/2 | **[Lean]** | `Proof/Edge.lean`, `majority_line`, `thr_sensitive`, `thr_survives` |
| V.4.5 | Unit thresholds: duality floor (e + 1)/2 | **[Lean]** | `Proof/CPDuality.lean`, `thr_duality` |
| V.4.6 | Weighted lines are cheap in both channels | **[Lean]** | `Proof/CPDuality.lean`, `two_cheap` |
| V.4.7 | Interpolation split: disjoint boundary laws iff unsatisfiable | **[Lean]** (logical core) + **[classical]** (interface bounds) | `Proof/CPDuality.lean`, `split_unsat_iff`; Pudlak 1997 |
| V.4.8 | Every CP refutation of a 3-CNF contains a creative pair; single roundings create nothing; additive pairs are cheap | **[Lean]** | `Proof/CPPairs.lean`, `creative_pair`, `round_single`, `fan_cheap` |
| V.4.9 | The all-1/2 point survives sums, not rounding; rank, not size; SOS degree does not transfer | **[Lean]** + **[classical]** | `Proof/CPDuality.lean`, `half_clause`, `half_breaks_rounding`; Grigoriev 2001; Dadush-Tiwari 2020 |
| V.4.10 | **Interface hardness at width 3** (equivalently a size-forcing cost measure W_CP) | **[open]** | `EDGE.md`, 0.4; `CP-DUALITY.md`, 0.5 |

## V.5 The native method and the floor

The native method makes each layer of a proof one decision and then computes: merge single-purpose lemmas, turn finite case analysis
into a checker proved equal to the statement, let automation carry regularity. Every pass lowers a natural-number measure, so the
method stops **[Lean]** (`fixed_after`); without quanta it would not (`real_never_arrives`). Depth contracts by 1/2 under pointer
jumping (`iterate_clog_pairUp`), while the total checking work is conserved (`sum_pairUp`) **[Lean]**. Applied to the bottom of the
`yang_mills_assembly` chain with the same statements re-checked: 16 theorems to 12, 5 layers to 4, term size -6 %, kernel time unchanged
within noise **[Lean]** + **[numerical]**.

| # | Result | Status | Source |
|---|---|---|---|
| V.5.1 | Quantized descent arrives; real descent need not; pointer jumping halves depth; work conserved (II.7) | **[Lean]** | `Native/Method.lean`, `fixed_after`, `real_never_arrives`, `iterate_clog_pairUp`, `sum_pairUp`, `reaches_floor` |
| V.5.2 | Applied to a real chain: same statements, 16 theorems to 12, 5 layers to 4 | **[Lean]** + **[numerical]** | `Native/RouteBChain.lean`; `NATIVE-METHOD.md`, 0.3 |
| V.5.3 | The method's floor is per proof and lies at or above the minimal refutation; the method bounds no minimum | **[reading]** | `NATIVE-METHOD.md`, 5 |
| V.5.4 | Finding a resolution refutation polynomial in the shortest one is NP-hard | **[classical]** | Atserias-Mueller 2019 |

## V.6 The open steps

| # | Open step | Form | Source |
|---|---|---|---|
| N1 | Is the irreducible core of every refutation polynomial in the question? (the size of the remnant) | NP vs coNP | `docs/OPEN-QUESTIONS-DMP.md`, 4 |
| N2 | Interface hardness at width 3 for cutting planes on random 3-CNF (V.4.10) | NP vs coNP, for CP | `EDGE.md`, 0.4; `CP-DUALITY.md`, 0.5 |
| N3 | Step T and step H for Frege: a short Frege refutation of a random 3-CNF yields a small separating formula for a balanced cut, and that pair has none of polynomial size (beyond the n^3 barrier) | NP vs coNP, for Frege | `DICHOTOMY-TRANSFER.md`, 4 to 6 |
| N4 | From the certified class to all inputs: is every instance's existence decidable cheaply? | P vs NP | `DICTIONARY.md`, 6.3, 8 |

N2 is new in this draft and is the sharpest: a named system, a named family and one missing object. It would not settle NP vs coNP
(CP is not the strongest system), but it is the first place where the structureless case meets a system strong enough to name a
crossing in one line.

## V.7 The barriers

**Every closing argument must pass three barriers** **[classical]**: relativization (Baker-Gill-Solovay 1975; the coupling proofs and
the gadget reductions both relativize), natural proofs (Razborov-Rudich 1997; "structureless means hard" is large and constructive
when stated about typical functions; V.4.2 avoids it by speaking about one formula), algebrization (Aaronson-Wigderson 2009;
partition-function polynomials and zero-free regions algebrize). Williams' route (2014) evades all three, but no faster-than-brute-force
satisfiability algorithm follows from local certification **[open]**.

## V.8 DMP readings attached to this part (all [reading])

* **Two categories of proof lines.** Lines derived directly from the axioms are cheap and mechanically checkable; new derivations
  (lemmas, cuts, extension variables) are what make short proofs possible, and eliminating them can blow a proof up exponentially.
  The owner's "first true act" is two new derivations used together, sharing existence but not possibility: in CP, the interpolation
  split (V.4.7) and the creative pair (V.4.8).
* **The pairs of derived lines are the entanglement through which the HTF acts in NP**: the size floor needs the pair to be charged at
  its interface (V.4.10).
* **The lower bound is confinement plus the needed uncertainty**: the size-width relation (V.3.4); in CP the uncertainty term collapses
  because one line aggregates its units (V.4.4), and W_CP is the missing term.
* **"P = NP within a DB, P != NP across it"**: the first half is V.1.8; the second is not proved (V.6).
* Describable => exists => positive: SAT iff #SAT > 0. A contradiction excised leaves "it does not exist": refutation completeness
  (V.3.1). Inward and outward reach: Dobrushin column and row sums.
* "A question with no structure has no basis/language in which to speak an answer": incompressibility of the one formula (V.4.2); the
  care point is the natural-proofs barrier, avoided only by speaking about the specific formula.

## V.9 What would close it

For NP vs coNP through proof complexity: superpolynomial lower bounds for every proof system, which would include N3 for Frege. The
nearest step is N2, interface hardness at width 3 for cutting planes, which would be a new lower bound for a natural system on the
structureless family, though not a resolution of NP vs coNP. For P vs NP: N4, a barrier-passing argument from the certified class to
all inputs. Nothing in this part closes any of them.
