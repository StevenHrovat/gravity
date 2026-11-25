# Part V. P vs NP: inside a certified class, and across it

*Draft 6. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/ProofPhase/`; notes relative to
`docs/pnp/`. Claim labels (V.n) are listed in `../CLAIMS.md`.*

**Plug in here.** Gives: the crossing theorem for sound two-premise proof systems, and where NP versus coNP stays open. Needs:
II.4.1, II.8 and II.14. Route: off both routes; read it for P versus NP. VIBE coefficient: it enters only as the bit: pointer jumping
halves the depth with each pass (II.15.2) and seven bits cannot single out a byte (`seven_bits_collide`, R.12l) **[Lean]**.

**As a statement checked step by step (II.4.1).** The statement is the card's open step, the crossing cost (`CrossingCost`),
checked at every step of the card's box (V.10) **[Lean]**; the inductive step is free and the open part is the base case. A passing
box gives every refutation at least e^(theta b) lines (`np_box_concl`).

## V.0 What is proved and what is not

**This part does not resolve P vs NP, nor NP vs coNP.** It proves, in Lean, the sampling side of the chain of II.8 for finite systems
(V.1) and the exact parts of the dichotomy for refutations (V.3). It then takes the strongest proof system in which the structureless
case is open, cutting planes on random 3-CNF, and locates the open step there to one missing cost measure (V.4, V.5). Every closing
argument must pass the relativization, natural-proofs and algebrization barriers (V.7).

Two notions of the problem are used:

* **P vs NP** (decision, search, counting): `DICTIONARY.md`.
* **NP vs coNP** via proof systems: a polynomially bounded proof system exists iff NP = coNP **[classical]** (Cook-Reckhow 1979);
  NP != coNP implies P != NP. `PROOF-SYSTEMS.md`. This part works on the NP vs coNP side, through proof complexity; that is why the abstract names
  NP versus coNP for this problem.

**The algebraic analogue.** On 23 November 2026 a proof that VP != VNP over every field, Valiant's algebraic analogue of P != NP,
was posted with a Lean 4 formalisation, credited to Claude (Anthropic): circuits for the Hamiltonian cycle polynomial over every
field, and for the permanent outside characteristic 2, need more than m^(c (log m)^(1/3)) gates (Anthropic 2026). Its own README
says that no human mathematician has checked the proof, that no machine checks that the Lean statement matches the paper, and that
it does not settle P vs NP **[external, unverified]** (claim V.0v). This paper uses nothing from it.

## V.3 Refutations: the dichotomy transferred (NP vs coNP)

A refutation proves that a formula has no satisfying assignment: the remnant "it does not exist". Resolution always finds one. For an expanding, minimally unsatisfiable formula (the two hypotheses of V.3.5), every refutation in
every sound two-premise system must, somewhere, cross from local facts to a global one (II.14.5). That crossing is universal in this
sense; its cost is not.

**Confinement times resolution (the size-width relation).** In resolution the cost of the crossing has two terms: the width the
crossing must assert (confinement: the cut principle, width at least the boundary), and the share of it one restriction resolves
(resolution). The DAG-like size-width relation is in Lean: if width w + d + b is impossible, for axioms of width at most w, every DAG-like refutation has size at
least exp(b (w + d + 1)/2n) **[Lean]** (`Proof/Dag.lean`, `size_width`, `size_width_exp`). With the cut principle the same bound
holds whenever w + d + b < e, e the boundary of every middle region **[Lean]** (`dag_size_ge`); optimising b gives
exp((e - w)^2 / 8n) up to rounding **[paper]**. This is Ben-Sasson-Wigderson (2001) **[classical]**, machine-checked here.

| # | Result | Status | Source |
|---|---|---|---|
| V.3.1 | Tree-like resolution is sound and refutation-complete: refutable iff unsatisfiable | **[Lean]** | `Proof/Resolution.lean`; `Proof/Complete.lean`, `refutable_iff` |
| V.3.2 | No inference creates assertion; every refutation has a middle-sized clause; resolution width is at least the boundary count (for formulas whose proper sub-systems are satisfiable and whose middle-sized sub-systems have a large sensitive boundary: the two hypotheses of V.3.5) | **[Lean]** | `Proof/Cut.lean`, `exists_middle`, `width_ge` |
| V.3.3 | Tree-like size-width: if no refutation of width W exists, every tree-like refutation has more than 2^{W - w} leaves (w the axiom width) | **[Lean]** | `Proof/SizeWidth.lean`, `tl_size_gt` |
| V.3.4 | DAG-like size-width: size >= exp(b (w + d + 1)/2n); with the cut principle for w + d + b < e, hence exp((e - w)^2 / 8n) | **[Lean]** (the optimisation over b **[paper]**; classical: Ben-Sasson-Wigderson 2001) | `Proof/Dag.lean`, `size_width`, `size_width_exp`, `dag_size_ge` |
| V.3.5 | Tseitin on expanders: resolution width at least the expansion, with two stated hypotheses (sub-systems satisfiable; expansion count) | **[Lean]** with hypotheses | `Proof/Tseitin.lean`, `width_ge`, `tl_size_ge` |
| II.14.2 | Gauss law mod 2: boundary parity equals interior charge; odd charge is unsatisfiable | **[Lean]** | `Proof/Crossing.lean`, `gauss`, `unsat_of_odd` |
| II.14.5 | **Every refutation crosses:** in every sound system with at most two premises per rule, every refutation of an expanding formula has a line sensitive to at least the expansion many variables | **[Lean]** with the two hypotheses (satisfiable sub-systems; unique-neighbour expansion), clause blocks included | `Proof/Crossing.lean`, `cross_any_system_of_falsify`, `fixes_of_single`, `invisible_of_not_mem` |
| V.3.8 | The crossing is universal, its cost is not: one XOR names the Tseitin flux; resolution pays 2^{b-1} clauses of width b for it, Frege about b^2 symbols | **[Lean]** (`summary`) / **[classical]** (standard counts: the CNF of an XOR of b variables; the balanced parity formula; recalled) | `DICHOTOMY-TRANSFER.md`, 3 |
| V.3.9 | Known lower bounds: resolution (Haken 1985; Urquhart 1987; Chvatal-Szemeredi 1988), bounded-depth Frege (Ajtai 1988; Pitassi-Beame-Impagliazzo 1993; Krajicek-Pudlak-Woods 1995), cutting planes (Pudlak 1997) | **[classical]** | `PROOF-SYSTEMS.md`, 2 |
| V.3.10 | Feasible interpolation for resolution and cutting planes; its failure for Frege and extended Frege under cryptographic assumptions | **[classical]** / **conditional** | Krajicek 1997; Pudlak 1997; Krajicek-Pudlak 1998; Bonet-Pitassi-Raz 2000 |
| V.3.11 | No superpolynomial lower bound is known for AC^0[p]-Frege, Frege or extended Frege (a statement about the literature, recalled) **[open]**; best de Morgan formula lower bounds about n^3 **[classical]** | **[open]** / **[classical]** | Krajicek, *Proof Complexity* (2019), recalled; formulas: Hastad 1998; Tal 2014 |

## V.6 The open steps

| # | Open step | Form | Source |
|---|---|---|---|
| N1 | Is the irreducible core of every refutation polynomial in the question? (the size of the remnant) | NP vs coNP | `docs/OPEN-QUESTIONS-DMP.md`, 4 |
| N2 | Interface hardness at width 3 for cutting planes on random 3-CNF (V.4.10) | NP vs coNP, for CP | `EDGE.md`, 0.4; `CP-DUALITY.md`, 0.5 |
| N3 | Step T and step H for Frege: a short Frege refutation of a random 3-CNF yields a small separating formula for a balanced cut, and that pair has none of polynomial size (beyond the n^3 barrier) | NP vs coNP, for Frege | `DICHOTOMY-TRANSFER.md`, 4 to 6 |
| N4 | From the certified class to all inputs: is every instance's existence decidable cheaply? | P vs NP | `DICTIONARY.md`, 6.3, 8 |

How the open steps relate. The Lean card's open step is `CrossingCost` (`API/NP.lean`): every refutation admits b restrictions,
each keeping at most a 1 - theta share of the costly lines. Lifting with a suitable constant gadget gives it for lifted formulas
(V.4.11, **[Lean]**); N2 would give it for random 3-CNF in cutting planes, but that implication is not stated in Lean. N1, N3 and N4
are further items, not instances of the card. N2 is the sharpest: a named system, a named family and one missing object. It would not settle NP vs coNP
(CP is not the strongest system), but it is the first place where the structureless case meets a system strong enough to name a
crossing in one line.

**The full text.** This part is contracted. Every derivation it leaves out is in the full Draft 6 at the git tag `d6-full`, and in Draft 5 section by section; every claim keeps its row, status and evidence in `../CLAIMS.md`.
