# Part IV. The generalised Riemann hypothesis: the positivity route

*Dense skeleton, draft 1, 2026-11-23. Every result with its status and source. Lean paths relative to
`docs/mass-gap/formal/ProofPhase/`; notes relative to `docs/rh-guide/`. Claim labels (IV.n) are listed in `../CLAIMS.md`.*

## IV.0 What is proved, by whom, and what this part does

**State of the problem (2026-11-23).**

* The Riemann hypothesis for zeta and GRH for every Dirichlet L-function are proved in Lean by others: a library released
  2026-11-20 and certified by the Lean and Mathlib communities on 2026-11-21 **[external]** (`SOURCES.md`, S1 to S4;
  `GUIDE.md`, section 1). This project read the main statements in the source and did not rebuild the library.
* GRH for Dedekind, Hecke and general automorphic L-functions is not proved **[open]** (`GUIDE.md`, sections 1 and 5).
* The proof by others does not go through positivity: its endgame is Landau's theorem, on a Stepanov-type size balance
  **[external, traced]** (`GUIDE.md`, sections 2, 4, 5).

**What this part does.** It follows the other road: Weil's positivity criterion, the second column of the chain of II.0. It proves
the chain in finite models, locates the one missing construction exactly, and gives it in five forms. **This part does not prove
GRH for any L-function.** Its value is a reduction that is independent of the existing proof and would, if closed, extend to
L-functions the existing proof does not reach.

## IV.1 The chain in finite models (links 1 to 4)

| # | Result | Status | Source |
|---|---|---|---|
| IV.1.1 | Finite Weil criterion: zeros closed under conjugation; the zero pairing is non-negative on every finite exponential sum iff every zero is on the line | **[Lean]** | `GRH/Weil.lean`, `weil_criterion_finite` |
| IV.1.2 | Zeros on the line imply the pairing is non-negative (each term is a square) | **[Lean]** | `GRH/Weil.lean`, `weilSum_re_nonneg_of_real` |
| IV.1.3 | Positivity implies the line for any test class with the approximation property (a named hypothesis) | **[Lean]** | `GRH/Weil.lean`, `real_of_weilSum_nonneg` |
| IV.1.4 | Weil's criterion for zeta and Dirichlet L-functions | **[classical]** | Weil 1952; Bombieri 2000 |
| IV.1.5 | For actual L-functions the Lean form needs the explicit formula and a zero count N(T) = O(T log T); Mathlib has neither | missing input, not a claim | `grh/ATTEMPT.md`, section 2 |
| IV.1.6 | A similitude multiplying a positive form by q has all eigenvalues of modulus sqrt q | **[Lean]** | `GRH/Orbits.lean`, `similitude_eigenvalue` |
| IV.1.7 | If Theta - 1/2 is skew-adjoint for a positive form, every eigenvalue has real part 1/2 (finite dimension) | **[Lean]** | `GRH/Orbits.lean`, `skew_shift_re_half` |
| IV.1.8 | **Without positivity the duality does not force the line:** an indefinite form is preserved by a mirror pair off the line (3/4 and 1/4) | **[Lean]** | `GRH/Orbits.lean`, `krein_off_line` |
| IV.1.9 | Lee-Yang circle theorem and Asano contraction, small cases | **[Lean]** | `GRH/LeeYang.lean`, `asano`, `ising3_zeros_on_circle` |
| IV.1.10 | Finite form of "remnants as evidence": fixed points of f^n are counted by points of exact period d dividing n | **[Lean]** | `GRH/Orbits.lean`, `card_fixed_pow_eq_sum` |

IV.1.8 is the one-line reason the whole route is about positivity: a mirror symmetry alone (the functional equation) never places
zeros on its axis.

## IV.2 The bridge: positivity locates singularities

| # | Result | Status | Source |
|---|---|---|---|
| IV.2.1 | Pringsheim, Landau, Laplace, spectral instances (Part II.3) | **[Lean]** | `Bridge/` |
| IV.2.2 | A positive transform cannot have a pole of negative residue approached from the right; ray form excludes real and complex zeros right of theta under a one-sided bound | **[Lean]** | `Bridge/Poles.lean`, `landau_ray_poles`, `lseries_residue_nonneg` |
| IV.2.3 | A real zero beta in (theta, 1) of L(chi, s) gives a pole of negative residue -m/(beta(1 - beta)) of a Mellin transform | **[classical]** (two-line computation; not formalised) | `bridge/BRIDGE.md`, 1.4; `bridge/ADDENDUM-STEP1.md` |
| IV.2.4 | Over function fields one positive duality (Hodge index; Rosati positivity) gives both the mirror axis and the balance point 1/2 | **[classical]** | Weil 1948; `bridge/BRIDGE.md`, 2.3 |
| IV.2.5 | In Stepanov's route and in the Lean proof by others the two 1/2s meet only in the conclusion | **[classical]** / **[external, traced]** | `bridge/BRIDGE.md`, 2.3 and 3 |
| IV.2.6 | **An arithmetic positivity in the role of the Hodge index, giving both 1/2s** | **[open]** | `bridge/BRIDGE.md`, section 4 |

Reading: "inversion and halving": every 1/2 in these formulas is the fixed point of an inversion (s -> 1 - s, alpha -> q/alpha,
m -> x/m) **[reading]**; one phenomenon only in Weil's route **[analogy]** elsewhere.

## IV.3 Measured: the shape of the missing positivity

| # | Result | Status | Source |
|---|---|---|---|
| IV.3.1 | Explicit formula normalisation agrees zero side vs prime side to about 1e-16 | **[numerical]** | `grh/weil_numerics.log` |
| IV.3.2 | Smallest eigenvalue of Weil's form on a 10-function space falls from 2.4e-1 (a = 0.15) to 2.6e-9 (a = 0.7), noise level at a >= 1; no violation seen | **[numerical]** | `grh/ATTEMPT.md`, section 4 |
| IV.3.3 | Semilocal test: Weil's form cut to a set S of places is positive only if S holds the real place and every prime up to e^{2a}; {2, 3} without the real place is negative everywhere tested | **[numerical]** | `grh/SEMILOCAL.md` |
| IV.3.4 | Prime-by-prime induction (Toeplitz frame, Szego recursion): each new prime acts only at the corner of the matrix; positivity holds iff the new entry lies within the current radius of the extrapolated value | **[classical]** + **[paper]** | `grh/INDUCTION.md`, sections 0 to 2 |
| IV.3.5 | Each prime step holds numerically up to a = 1.25 (reflection coefficients at most 0.68) | **[numerical]** | `grh/INDUCTION.md`, section 2 |
| IV.3.6 | A prime's own term is up to hundreds of radii (about -722 for p = 7) and the extrapolation cancels all but less than one: **every step is an exact cancellation** | **[numerical]** | `grh/INDUCTION.md`, section 2 |
| IV.3.7 | Scaling one weight by (1 + eta) breaks positivity at eta of order 1e-3 to 1e-9: continuous estimates cannot carry the step | **[numerical]** | `grh/INDUCTION.md`, section 4 |
| IV.3.8 | Weight positivity (Lambda(n) >= 0, Phi(u) > 0, Euler product) is provably not enough; de Bruijn-Newman Lambda = 0 sits exactly at the edge | **[classical]** + **[paper]** | `grh/LEE-YANG.md`, 5; Polya 1926; Rodgers-Tao 2020 |

## IV.4 The open step, in five forms

The missing piece: a positive object built from the primes, the characters and the real place alone, without the zeros.

| Form | Statement | Status | Source |
|---|---|---|---|
| 1 (weakest) | A Hilbert space H_chi and a map Phi from test functions, built from arithmetic data only, with <Phi f, Phi g> = W_chi(f * g~). By Weil and GNS it exists iff GRH holds for chi | **[open]** | `grh/ATTEMPT.md`, step 4 |
| 2 | A lattice ferromagnet at its critical coupling whose block-spin law is Riemann's Phi; RH by Newman's closure | **[open]** | `grh/LEE-YANG.md`, 5c |
| 3 | A foliated space whose closed orbits are the primes, with a positive leafwise Hodge form (Deninger) | **[open]** | `grh/ORBITS.md`, step 6 |
| 4 | A local rule predicting each new reflection coefficient inside the unit disc from arithmetic up to its scale | **[open]** | `grh/INDUCTION.md`, section 7 |
| 5 | A Hermite-Biehler coupling of xi's real and imaginary parts (de Branges framework; the specific de Branges conjecture is false, Conrey-Li 2000) | **[open]**; framework **[classical]** | `grh/INDUCTION.md`, section 5 |

Forms 2 and 3 each imply form 1; the five are not shown to be equivalent **[paper]** (`grh/INDUCTION.md`, 7; `grh/ORBITS.md`, 4).
Constraint from IV.3.3 and IV.3.6: the construction cannot add one prime at a time with slack; all primes up to the scale and the
real place must enter together, through an exact identity.

## IV.5 DMP readings attached to this part (all [reading])

* Positivity is the corollary "something exists"; forced existence lands on the prescribed line (I.1, I.2).
* The real place is the partner that carries existence: per place the primes give mean-zero wobbles and the real place the positive
  mean log(r / 2 pi) (supported by IV.3.3, **[numerical]**).
* "What GRH is missing is its concept of the remnant of acts": the periodic-orbit reading of the primes (form 3).
* "The act must entangle the real with the imaginary through a coupling factor": form 5.
* "Arithmetic exists but never runs": there is no Frobenius over Z (classical); running it as content is form 2.

## IV.6 What would close it

Any one of the five forms, built without the zeros. The Yang-Mills chain (Part III) is the model: there the positive object (e^{-S}
with locality) is given by construction, and reflection positivity follows. The open step here is to find the arithmetic G0 in
which Weil positivity is a construction rather than a conclusion (Part VI).
