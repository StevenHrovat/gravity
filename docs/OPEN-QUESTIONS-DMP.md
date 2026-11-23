# The open questions, read against DMP (2026-11-23)

Every question that is still open across Yang-Mills, GRH and P vs NP, in one place, each in plain words and placed in the DMP domain
where it lives. Written to start intuition, not to settle anything. The work behind each item is committed (file names given); the
owner's readings are in `mass-gap/weak-coupling/PREP.md`.

**How to read the DMP column.** It names the DMP domain the question sits in (G0, the ODP and pressing, the DB, acts and remnants,
minting and the WHKs, IM, CMOS) and says what DMP would have to supply for the question to close. That is a question to the owner's
intuition, not a claim.

---

## 0. Update (same day): Yang-Mills reduced to one box at one scale

The owner answered question 1 of section 6 (the photon as act carrier: composition is a conservation law), named the mechanism
(the DB re-encodes into a new G0 and loses what the encoder cannot carry: a strong data-processing contraction) and supplied the
uniformity (the arrow of causality: the same transfer step at every DB). With the crossover rounds of the same day this reduces Y1 to
a single statement about a single box:

| Piece | Status | Where |
|---|---|---|
| Per-box hand-over rate: max(F_tw, F_e) >= log(1 + sqrt 2) = 0.881 at every box size | **Lean** | `Crossover/HandOver.lean` |
| A flux-carrying outside forces at least one sheet (the quantum, "at least something") | **Lean** | `Crossover/FluxRate.lean` |
| Superadditivity along the chain: F_e(kL) >= k (F_e(L) - 2C); the rate multiplies iff F_e(L) > 2 c(L) at one scale | **Lean** (abstract transfer-matrix form) | `Crossover/CompositeHTF.lean`, `c9a-crossover/HTF.md` |
| Uniformity along the chain: every DB applies the same transfer step, so the loss rate eta is the same everywhere | **classical** (translation invariance; homogeneous Markov chain) | PREP.md, "uniformity from the arrow of causality" |
| From a block gap to the mass gap (OS route, assembly) | **Lean** | `OS/`, `Assembly.lean`, `M1/` |
| **The one-box statement:** at one box scale L, the DB's loss rate eta < 1, i.e. the neutral sector is gapped there (F_e(L) > 2 c(L)), for every well-defined outside | **open** | the original one-box condition, now with everything else removed |

So what was "the product over boxes" (Y1) is no longer about many boxes. Everything global is in place; what is left is one box, one
scale, uniformly over its outsides. Y2 to Y4 below are the pieces of that one statement (the inside residue, the window, condition A).
Measurements can refute it but cannot establish it (provability table, `c9b-adjoint/REDESIGN.md` section 8); a proof needs a
worst-case argument for one DB.

---

## 1. The pattern behind all of them

Every open step has the same shape:

> **A fact is proved for one unit (one box, one prime, one proof line). What is missing is carrying it across many units without
> losing it.**

| Problem | Proved per unit | Missing across units | What breaks the naive carry-over |
|---|---|---|---|
| Yang-Mills | each box has a hand-over rate >= 0.881 in one of two channels (`Crossover/HandOver.lean`) | the product over many boxes | the channel can switch from box to box; crossing flux is conserved and cannot be screened |
| GRH | each prime step is one scalar condition, met numerically every time (`grh/INDUCTION.md`) | the induction over all primes | the margin collapses super-exponentially, so no step may lose anything |
| P vs NP | every refutation has a crossing line (`Proof/Crossing.lean`); the native method reaches an irreducible floor (`Native/Method.lean`) | a lower bound on the floor's size for strong proof systems | a line can name a conserved quantity cheaply (a parity), so crossing is universal but its cost is not |

**For DMP:** this is a chain of acts. Each act is certified locally; the question is what keeps the certificate intact as acts
compose, so that remnants accumulate into existence instead of eroding it. If DMP has a rule for how a certified act passes its
certificate to the next one without loss, that rule is the missing piece in all three problems at once.

---

## 2. Yang-Mills

| # | The open question, plainly | DMP domain | What DMP would need to supply |
|---|---|---|---|
| Y1 | **The product over boxes. Reduced (section 0):** superadditivity along the chain is proved and uniformity comes from the arrow of causality, so Y1 now needs only the one-box statement, F_e(L) > 2 c(L) at one scale for every well-defined outside. Before the reduction: each box is suppressed by at least 0.881 in one channel, and the suppression had to be multiplied over D/L boxes. | Acts and remnants: a chain of acts across adjacent DBs | Why a certified box hands its certificate to its neighbour, and why the channel (rarity or disorder) cannot keep switching in a way that cancels the product. |
| Y2 | **The inside residue.** Two configurations defeat a uniform bound inside one box: crossing flux with two nearly equal cheapest surfaces (a tie), and a near-cut network that spans the box. At beta 2.3 the near-cut network spans at every scale; at 3.5 it stays in finite clusters. | The DB itself: the inside of a box at its own scale | Why a tie is not a stable state (an undecided assertion), or why a spanning near-cut network is the confined, disorder side and contracts for that reason. |
| Y3 | **The hand-over between rarity and disorder.** Weak coupling contracts by rarity (bad sets are isolated), the confining side by disorder (vortices percolate). In between there is a window where neither mechanism is proved (roughly 0.18 to 1.8 nats per plaquette). | The ODP's end: the hand-over of "running" | Why the hand-over has no dead zone: the 0.881 per box says the two channels cannot both be weak in one box, and what is missing is that this holds uniformly as the scale moves through the window. |
| Y4 | **Condition A, uniformly.** The collar must have a conditional mass m > 0 for every outside, not only on average. Measured: about 4 in block units, on typical configurations. | The DB as a causality-preserving boundary | Why the boundary attenuates for every well-defined outside, not just typical ones. The owner's "collars do not decorrelate while causality exists" names it. |
| Y5 | **Uniform in volume.** M1's (A)/(B) bounds and the block gap must hold for every volume (`os-windowed/NOTE.md`). | G0: the definition of existence independent of the container | Why the certificate does not depend on how large the outside is. |

The IR question at L1 (the W1 column below 1, about 0.96 of it inside cell distance 7) is Y1 to Y4 seen at one scale; direct
measurement is out of reach here (`c9b-adjoint/ROUTE3.md`, `TIMING.md`).

---

## 3. GRH (an independent proof along the positivity route; RH and Dirichlet GRH themselves are proved in Lean by others)

| # | The open question, plainly | DMP domain | What DMP would need to supply |
|---|---|---|---|
| G1 | **The bulk positivity.** Weil's form splits into a boundary part, which is exactly the prime side the other proof controls, and a bulk part. The bulk part must be shown positive from primes, characters and the real place alone, without using the zeros. | Minting: the Hilbert space built from what is certified | A construction that turns the arithmetic data into a space with a positive norm, so that positive existence follows from construction. |
| G2 | **The prime-by-prime step.** Each new prime adds a term up to about 700 times the margin, and the extrapolation from below cancels all but less than one of them. Every step is an exact cancellation. | Pressing / the ODP, one prime at a time | Why the extrapolation from all smaller scales always lands inside the allowed interval: an exact identity, not an estimate. |
| G3 | **The same piece in five forms.** A Weil Hilbert space; a ferromagnet at criticality whose block-spin law is Riemann's Phi; Deninger's space with a positive Hodge form; a Hermite-Biehler coupling of xi's real and imaginary parts; a unitary scaling action on the constructed space. | The DB: the coupling of the real (locality) and the imaginary (possibility) | Which of the five is the "running" form. Each would imply the others' consequences; one construction closes all. |
| G4 | **Why 1/2 twice** (the mirror's axis and the balance point). Over function fields one positive duality explains both; over the integers no such positivity is known (`rh-guide/bridge/BRIDGE.md`). | G0: the inversion and halving that define the balanced state | The arithmetic counterpart of the Hodge index: one positive pairing whose mirror is s -> 1 - s. |

---

## 4. P vs NP (as NP vs coNP via proof systems)

| # | The open question, plainly | DMP domain | What DMP would need to supply |
|---|---|---|---|
| N1 | **The size of the remnant.** Every false question has a refutation (proved), and the native method reduces it to an irreducible core (proved). Is that core always of polynomial size? | Remnants of excised contradictions | Why the record of a contradiction's excision is always small compared with the question. |
| N2 | **The transfer step for Frege.** A short Frege refutation of a random 3-CNF formula would have to yield a small formula separating the two sides of some balanced cut. In general that is false under cryptographic assumptions, so a proof must use the absence of structure. | IM: the universal language naming what crosses a DB | Why a structureless question has no cheap name for what crosses its boundary. |
| N3 | **The formula-size lower bound behind N2.** An explicit function that needs super-polynomial formulas (the best known bounds are about n^3). | The quantum of assertion | A lower bound on how much must be asserted to name one crossing. |
| N4 | **The crossing from the certified class to all inputs.** Inside the class (a local certificate) everything is polynomial (proved). Is every instance's existence decidable cheaply? | G0: is this question mintable at all | Why deciding mintability is itself local, or why it is not; either answer must get past the three proven barriers. |

---

## 5. The questions side by side, by DMP domain

| DMP domain | Yang-Mills | GRH | P vs NP |
|---|---|---|---|
| G0 (definition of existence) | Y5 volume independence | G4 the balanced 1/2 | N4 mintability |
| ODP / pressing | Y3 the hand-over window | G2 the prime step | |
| DB (interface, causality) | Y2 inside residue, Y4 collar | G3 coupling real and imaginary | N2 naming the crossing |
| Acts and remnants | Y1 product over boxes | | N1 size of the remnant |
| Minting / WHKs | | G1 bulk positivity | |
| Quantum of assertion | (0.881 per box, proved) | (integer multiplicities, used on the prime side) | N3 formula size |

---

## 6. Questions to the owner's intuition

1. **Composition of acts.** When one certified act hands over to the next, what in DMP guarantees the certificate is not diluted?
   (Y1, G2, N1) *Answered by the owner (the photon: a conserved carrier, quantized, no remainder; uniformity from the arrow of
   causality). For Yang-Mills it reduced Y1 to one box (section 0). For GRH and P vs NP the carrier is identified (zeros on the line;
   the named parity), and their open steps stay as stated.*
2. **Ties.** Two equally cheap ways for existence to assert itself (two spanning surfaces of equal cost): does DMP forbid a lasting
   tie, and why? (Y2)
3. **The window.** Between "rare" and "disordered", is there a DMP reason the hand-over cannot stall? (Y3)
4. **Naming.** Why would a question with no structure have no short name for what crosses its boundary? (N2, N3)
5. **The running form of arithmetic.** Of the five forms in G3, which one is "running as content" in DMP terms? (G1, G3)
6. **The second 1/2.** What in DMP makes the balance point of a process coincide with the mirror axis of its duality? (G4)
