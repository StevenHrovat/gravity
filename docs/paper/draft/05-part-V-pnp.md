# Part V. P vs NP: inside a certified class, and across it

*Dense skeleton, draft 1, 2026-11-23. Every result with its status and source. Lean paths relative to
`docs/mass-gap/formal/ProofPhase/`; notes relative to `docs/pnp/`. Claim labels (V.n) are listed in `../CLAIMS.md`.*

## V.0 What is proved and what is not

**This part does not resolve P vs NP, nor NP vs coNP.** It proves, in Lean, the sampling side of the chain of II.0 for finite
systems, and the exact parts of the dichotomy for refutations. It places the open problem precisely in two forms: the crossing
from a certified class to all inputs (decision and counting), and the cost of naming a conserved crossing flux in strong proof
systems (NP vs coNP via proof complexity). Both must pass the relativization, natural-proofs and algebrization barriers.

Two notions of the problem are used:

* **P vs NP** (decision, search, counting): `DICTIONARY.md`.
* **NP vs coNP** via proof systems: a polynomially bounded proof system exists iff NP = coNP **[classical]** (Cook-Reckhow 1979);
  NP != coNP implies P != NP. `PROOF-SYSTEMS.md`.

## V.1 Inside a certified class: the chain holds (links 1 to 4)

| # | Result | Status | Source |
|---|---|---|---|
| V.1.1 | Dobrushin column sums at most alpha < 1 (finite system, positive weights): the heat-bath sampler is within n alpha^t of equilibrium after t sweeps | **[Lean]** | `Mixing/Classical.lean`, `mixing_sweep_dobrushin`; `Mixing/Glauber.lean` |
| V.1.2 | The same condition gives a spectral gap of at least (1 - alpha)/n per single-site step | **[Lean]** | `Mixing/FiniteSpectral.lean`, `spectral_gap_dobrushin` |
| V.1.3 | Gap in time iff no spectral mass above e^{-m} | **[Lean]** | `Mixing/TimeGap.lean`, `time_gap_iff` |
| V.1.4 | Doeblin contraction and homogeneous chains (II.4) | **[Lean]** | `Mixing/Doeblin.lean`, `Mixing/Chain.lean` |
| V.1.5 | Dobrushin condition gives a unique Gibbs state; spatial mixing gives a volume-uniform gap | **[classical]** | Dobrushin 1968, 1970; Stroock-Zegarlinski 1992; Martinelli-Olivieri 1994 |
| V.1.6 | Polynomial sampling gives polynomial approximate counting for self-reducible problems, and back | **[classical]** | Jerrum-Valiant-Vazirani 1986 |
| V.1.7 | Hard-core model below lambda_c(D): deterministic counting (correlation decay) and O(n log n) mixing | **[classical]** | Weitz 2006; Anari-Liu-Oveis Gharan 2020; Chen-Liu-Vigoda 2021 |
| V.1.8 | **The certified class** (influence sums below alpha after blocking, or the Lovasz local lemma condition): existence guaranteed, search, sampling and approximate counting polynomial | **[classical]** assembled; mixing step **[Lean]** | `DICTIONARY.md`, 6.2; Lovasz 1975; Moser-Tardos 2010; Moitra 2019 |
| V.1.9 | Identifying this class with "inputs whose existence is described by a DMP-complete system" | **[reading]** | `DICTIONARY.md`, 6.1 |

DMP reading: "P = NP within a DB" is V.1.8 **[reading]**; "P != NP across a DB" is not proved (V.4).

## V.2 At the edge of the class: what is known to go wrong

| # | Result | Status | Source |
|---|---|---|---|
| V.2.1 | Antiferromagnetic two-spin systems beyond uniqueness: no FPRAS unless NP = RP | **conditional** (NP != RP) | Sly 2010; Sly-Sun 2014; Galanis-Stefankovic-Vigoda 2015, 2016 |
| V.2.2 | Bounded-degree k-CNF: approximate counting NP-hard above degree c 2^{k/2} | **conditional** | Bezakova-Galanis-Goldberg-Guo-Stefankovic 2019 |
| V.2.3 | The ferromagnetic Ising model loses uniqueness but keeps an FPRAS at every temperature | **[classical]** | Jerrum-Sinclair 1993 |
| V.2.4 | Lattice gauge theory with the Wilson action is on the ferromagnetic side: slow dynamics at phase boundaries but no NP-hardness from coexistence is predicted | **[reading]** | `DICTIONARY.md`, 5 |
| V.2.5 | Putting all counting instances inside the uniqueness region is as strong as NP = RP; reducing SAT into the LLL class is impossible as stated (all LLL instances are satisfiable) | **conditional** / **[classical]** | `DICTIONARY.md`, 6.3 |

## V.3 Refutations: the dichotomy transferred (NP vs coNP)

| # | Result | Status | Source |
|---|---|---|---|
| V.3.1 | Resolution is sound and refutation-complete: refutable iff unsatisfiable (the remnant "it does not exist" always exists) | **[Lean]** | `Proof/Resolution.lean`; `Proof/Complete.lean`, `refutable_iff` |
| V.3.2 | No inference creates assertion; every refutation has a middle-sized clause; resolution width is at least the boundary count | **[Lean]** | `Proof/Cut.lean`, `exists_middle`, `width_ge` |
| V.3.3 | Tree-like size-width: width W forces more than 2^{W - w} leaves | **[Lean]** | `Proof/SizeWidth.lean`, `tl_size_gt` |
| V.3.4 | DAG size-width: size at least exp((W - w)^2 / 8n) | **[classical]** | Ben-Sasson-Wigderson 2001 |
| V.3.5 | Tseitin on expanders: resolution width at least the expansion; with two stated hypotheses (sub-systems satisfiable; expansion count) | **[Lean]** with hypotheses | `Proof/Tseitin.lean`, `width_ge`, `tl_size_ge` |
| V.3.6 | Gauss law mod 2: boundary parity equals interior charge; odd charge is unsatisfiable | **[Lean]** | `Proof/Crossing.lean`, `gauss`, `unsat_of_odd` |
| V.3.7 | **Every refutation crosses:** in every sound system with at most two premises per rule, every refutation of an expanding formula has a line sensitive to at least the expansion many variables | **[Lean]** with the two hypotheses of V.3.5 | `Proof/Crossing.lean`, `cross_any_system` |
| V.3.8 | The crossing is universal, its cost is not: one XOR names the Tseitin flux; resolution pays 2^{b-1} clauses of width b for it, Frege about b^2 symbols | **[Lean]** (`summary`) / **[classical]** | `DICHOTOMY-TRANSFER.md`, 3 |
| V.3.9 | Known lower bounds: resolution (Haken 1985; Urquhart 1987; Chvatal-Szemeredi 1988), bounded-depth Frege (Ajtai 1988; Pitassi-Beame-Impagliazzo 1993; Krajicek-Pudlak-Woods 1995), cutting planes (Pudlak 1997) | **[classical]** | `PROOF-SYSTEMS.md`, 2 |
| V.3.10 | Feasible interpolation for resolution and cutting planes; its failure for Frege and extended Frege under cryptographic assumptions | **[classical]** / **conditional** | Krajicek 1997; Pudlak 1997; Krajicek-Pudlak 1998; Bonet-Pitassi-Raz 2000 |
| V.3.11 | No superpolynomial lower bound is known for AC^0[p]-Frege, Frege or extended Frege; best formula lower bounds about n^3 | **[open]** / **[classical]** | Hastad 1998; Tal 2014 |
| V.3.12 | The flux-loss principle reproduces Urquhart's bound for resolution; for Frege its crossing-cost step is as hard as explicit formula lower bounds | **[reading]** on **[classical]** | `PROOF-SYSTEMS.md`, 6 |

## V.4 The native method and the floor

| # | Result | Status | Source |
|---|---|---|---|
| V.4.1 | Quantized descent arrives; real descent need not; pointer jumping halves depth (II.7) | **[Lean]** | `Native/Method.lean` |
| V.4.2 | Applied to a real chain: same statements kernel-checked, 16 theorems to 12, 5 layers to 4 | **[Lean]** + **[numerical]** | `Native/RouteBChain.lean`; `NATIVE-METHOD.md`, 4 |
| V.4.3 | The method's floor is per proof and lies at or above the minimal refutation; the method bounds no minimum | **[reading]** | `NATIVE-METHOD.md`, 5 |
| V.4.4 | Finding a resolution refutation polynomial in the shortest one is NP-hard | **[classical]** | Atserias-Mueller 2019 |

## V.5 The open steps

| # | Open step | Form | Source |
|---|---|---|---|
| N1 | Is the irreducible core of every refutation polynomial in the question? (the size of the remnant) | NP vs coNP | `OPEN-QUESTIONS-DMP.md`, 4 |
| N2 | Step T: a short Frege refutation of a random 3-CNF yields a small formula separating the two sides of a balanced cut | NP vs coNP, for Frege | `DICHOTOMY-TRANSFER.md`, 5, 6 |
| N3 | Step H: that pair has no polynomial-size separating formula (beyond the n^3 barrier) | formula lower bound | `DICHOTOMY-TRANSFER.md`, 4 to 6 |
| N4 | From the certified class to all inputs: is every instance's existence decidable cheaply? | P vs NP | `DICTIONARY.md`, 6.3, 8 |

**Barriers every closing argument must pass** **[classical]**: relativization (Baker-Gill-Solovay 1975; the coupling proofs and the
gadget reductions both relativize), natural proofs (Razborov-Rudich 1997; "structureless means hard" is large and constructive),
algebrization (Aaronson-Wigderson 2009; partition-function polynomials and zero-free regions algebrize). Williams' route (2014)
evades all three, but no faster-than-brute-force satisfiability algorithm follows from local certification **[open]**.

## V.6 DMP readings attached to this part (all [reading])

* Describable => exists => positive: SAT iff #SAT > 0; Goedel completeness for consistent descriptions.
* A contradiction excised leaves "it does not exist": refutation completeness (V.3.1).
* "The lower bound to NP = coNP is the flux loss of the assertion of existence": V.3.12.
* "A question with no structure has no basis/language in which to speak an answer": incompressibility; the care point is the
  natural-proofs barrier (it must use the specific family, not typical functions).
* Inward and outward reach: Dobrushin column sums (influence received) and row sums (influence given).
