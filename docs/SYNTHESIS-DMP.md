# DMP across Yang-Mills, GRH and P vs NP: a synthesis (2026-11-23)

One page that collects the owner's readings of 2026-11-23 and what each one meets in mathematics and physics. The full entries,
with the owner's exact words, are in `mass-gap/weak-coupling/PREP.md` (the entries of that date). This page adds nothing new; it
sorts what is there.

**Marks.** **Lean**: proved in this repository, standard axioms only. **Classical**: known mathematics or physics. **Reading**: an
interpretation that maps a DMP statement onto a known structure. **Open**: not settled. A DMP reading is never stated here as a
mathematical result.

---

## 1. The one chain behind all three problems

| Step | DMP | Yang-Mills | GRH | P vs NP |
|---|---|---|---|---|
| 1. Something exists | existence = non-existence + 1; describable => exists | Z > 0, positive Boltzmann weights | a positive pairing of test functions | SAT iff #SAT > 0 (Z > 0) |
| 2. Positivity builds a space | pressing to G0 before use | reflection positivity -> OS Hilbert space (Lean, `M1/UVTVOS`, `OS/`) | Weil positivity -> GNS space (Lean, finite model, `GRH/Weil`) | positive weights -> L2 space of the sampler (Lean, `Mixing/FiniteSpectral`) |
| 3. The space carries an evolution | the act, the tick | transfer matrix e^{-H}, H >= 0 | translation in log-scale time | the heat-bath operator, 0 <= P <= 1 |
| 4. Positivity pins the spectrum | the gap as a binary certificate | mass gap = decay rate (Lean, `Bridge/Spectral`) | real spectrum = zeros on the line | spectral gap = fast mixing (Lean, `Mixing/`) |
| 5. One finite check certifies all scales | pressing, then minting | one-box contraction at one scale (Dobrushin column < 1) | (no finite check known) | the local certificate of the class theorem |

**Reading.** The direction 1 -> 4 is a theorem in each column. What is open in each problem is step 1 or 2 for the hard case:
establishing the positivity, not using it.

---

## 2. Yang-Mills

| Reading | Counterpart | Status |
|---|---|---|
| Dimensions of existence: a space half and a direction half, coupled but not entangled | OS: time slice (states) and one reflection direction (transfer matrix); two time directions give an indefinite norm | Classical |
| Only 3+1 transmutes | g^2 dimensionless only in d = 4; d = 4 enters Lean only as counting, physically in Balaban's scaling and the vortex-sheet count | Classical; audit (`GENERALISE-AUDIT.md`) |
| N-alities; SU(2) is self-dual, SU(3) a neutral class plus a dual pair | centre Z_N, classes k and N - k paired by conjugation; SU(2)'s fundamental is pseudo-real | Classical; Lean SU(N) package (`General/`) |
| Higher N-alities contain lower ones only by divisibility | Z_M in Z_N iff M divides N; an embedded SU(2) loses its centre in SU(3) | Classical |
| Pressing and minting | pressing = scale-by-scale construction until the one-box certificate passes; minting = the windowed OS route and the limits | Reading; minting done in Lean, pressing open |
| The gap is binary, any gap is the same gap from inside | the claim is "some Delta > 0"; with one scale the value is a unit choice, only ratios are internal | Classical |
| WHKs (White Hole Keys): each part derives the others | no free dimensionless parameter: group + one scale fix everything | Classical |
| Weak coupling: cheapest per tick, but the continuum is the most expensive point | continuum at g -> 0, universality; cost ~ (L/a)^4 tau / margin^2 | Classical; measured in the IR pre-step |
| Small influences trend to an irreducible minimum | positive weights: irreducible chain, one running state; influences never exactly zero | Classical; W2 data consistent |

---

## 3. GRH

| Reading | Counterpart | Status |
|---|---|---|
| Inversion and halving | every 1/2 is the fixed point of an inversion: s -> 1 - s, alpha -> q/alpha, m -> x/m | Classical (`rh-guide/bridge/BRIDGE.md`) |
| The two 1/2s (mirror axis and balance point) | one positive duality explains both over function fields (Weil, Hodge index); in Stepanov's route and the Lean RH proof they meet only in the conclusion | Classical; missing: an arithmetic Hodge index |
| Positivity is "something exists" | Weil's criterion: positivity of the explicit-formula pairing iff GRH | Lean in a finite model (`GRH/Weil.lean`) |
| -1/12 and the halving | the bulk Gamma term and zeta(-k) are two halves of one regulated sum; -1/12 enters YM as the Luescher term | Classical |
| The reals are binary (Dedekind cuts), derivable from any frame | categoricity of the complete ordered field; the reals' first-order theory is decidable (Tarski) | Classical |
| Multiplication is a DB crossing; i lets a real cross to its opposite | -1 = i x i avoids 0; addition alone and multiplication alone are decidable, together not | Classical |
| The real place is the partner that carries existence | per place: primes give mean-zero wobbles, the real place gives the positive mean log(r / 2 pi); {2, 3} alone is negative everywhere | Numerical (`grh/SEMILOCAL.md`) |
| Primes as free U(1) phases | log p independent over Q; Kronecker, Voronin universality | Classical |
| Arithmetic exists but never runs; run it as content | no Frobenius over Z; primon gas, Bost-Connes, Lee-Yang, de Bruijn-Newman (RH iff Lambda <= 0; 0 <= Lambda <= 0.22) | Classical; study under way (`grh/LEE-YANG.md`) |
| Euler's number and Euclidean time as the attachment point | Wick rotation between the prime-side (Laplace) and zero-side (Fourier) positivities | Reading on classical facts |

**Where it stops (open):** a Hilbert-space representation of Weil's form built from primes and the real place alone
(`grh/ATTEMPT.md`, step 4). It is equivalent to GRH. The margin collapses super-exponentially, so only an exact identity can work.

---

## 4. P vs NP

| Reading | Counterpart | Status |
|---|---|---|
| P = NP within a DB, P != NP across | uniqueness: polynomial sampling and counting; beyond it, NP-hard counting for antiferromagnets (assuming NP != RP) | Lean for the inside (`Mixing/`); conditional for the outside |
| A sane polynomial | marginal, bounded-below actions; column < 1 = polynomial-time sampling | Classical; Lean |
| Inputs whose existence is described by DMP-complete systems | a promise class with a local certificate: existence guaranteed, search, sampling and counting polynomial | Classical, assembled (`pnp/DICTIONARY.md` 6) |
| Valid input = existing (mintable) input | on that domain the class theorem holds; "is this instance mintable?" is the NP-complete question itself | Reading |
| Describable => exists => positive | SAT iff Z > 0; Goedel completeness for consistent descriptions | Classical |
| Undecidability is not inevitable | a complete, effectively axiomatised theory is decidable (reals: yes; integers with x: no) | Classical |
| Inward and outward reach | Dobrushin column sums (influence received) and row sums (influence given) | Lean (`Mixing/Classical.lean`) |

**Where it stops (open):** crossing from the certified class to all inputs. Collapse is ruled out for decision and as strong as
NP = RP for counting. A separation must pass the relativization, natural-proofs and algebrization barriers.

---

## 5. Time, boundaries and the inside

| Reading | Counterpart | Status |
|---|---|---|
| The DB translates inside (Euclidean) time into the outside clock | Hawking: smoothness at the horizon fixes the Euclidean period 2 pi / kappa; Tolman: T sqrt(g_00) = const is time dilation | Classical |
| Remnants at the DB slow the assertion | settling time set by the slowest collective objects (topological freezing) | Classical; settling test on W2 pending |
| Aperiodicity from CMOS inside confined non-existence | the CMOS is the tick; the null option (no change within a tick) gives aperiodicity | Classical |
| Contained in a larger existence, at least +1 | strict flip bound Z_tw < Z (Lean, `Flip/Strict.lean`); Cantor: the description of all parts is strictly larger | Lean; classical |
| Simulations must give out provable statements | every measured quantity is mapped to the statement it would discharge; a PASS alone discharges nothing (for-all statements), a FAIL refutes | Design rule (`c9b-adjoint/REDESIGN.md` 8, `w2/RESULT.md`) |

---

## 6. The open steps, side by side

| Problem | The open step | What would close it |
|---|---|---|
| Yang-Mills | the crossover P4 and the IR column below 1 at a certified scale, uniformly in volume | a worst-case argument for the one-box condition; measurements can only refute or guide |
| GRH | a zero-free arithmetic Hilbert space for Weil's form | an arithmetic positivity (Hodge-index type) or a reflection-positive system running xi |
| P vs NP | from the certified class to all inputs | a non-relativizing, non-natural, non-algebrizing argument |
| Bridge | why the two 1/2s coincide over the integers | the same arithmetic positivity as for GRH |

**Reading.** The four open steps have one shape: a positivity (or certificate) that is known locally or in a model and must be
established for every case. The Yang-Mills proof is the one project where the positivity is given by construction (e^{-S} >= 0
plus locality), which is why it is the model the other two borrow from.
