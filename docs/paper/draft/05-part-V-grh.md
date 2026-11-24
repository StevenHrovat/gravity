# Part V. The generalised Riemann hypothesis: the positivity route

*Draft 2, 2026-11-23. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/ProofPhase/`; notes relative to
`docs/rh-guide/`. Claim labels (IV.n) are listed in `../CLAIMS.md`.*

## V.0 What is proved, by whom, and what this part does

**State of the problem (2026-11-23).**

* The Riemann hypothesis for zeta and GRH for every Dirichlet L-function are proved in Lean by others: a library released
  2026-11-20 and certified by the Lean and Mathlib communities on 2026-11-21 **[external]** (`SOURCES.md`, S1 to S4; `GUIDE.md`,
  section 1). This project read the main statements in the source and did not rebuild the library.
* GRH for Dedekind, Hecke and general automorphic L-functions is not proved **[open]** (`GUIDE.md`, sections 1 and 5).
* The proof by others does not go through positivity. Its endgame is Landau's theorem applied to a one-sided square-root bound on the
  prime count, obtained from a Stepanov-type size balance **[external, traced]** (`GUIDE.md`, sections 2, 4, 5).

**What this part does.** It follows the other road: Weil's positivity criterion, the second column of the chain of II.8. It proves the
chain in finite models (V.1), shows exactly why a mirror symmetry alone cannot place zeros on the line (V.2), measures the shape of
the missing positivity (V.3), and states the one missing construction in eight equivalent-looking faces (V.4), with "it runs" as the
form shared with Yang-Mills (V.5). **This part does not prove GRH for any L-function.** Its value is a reduction that is independent of
the existing proof and would, if closed, extend to L-functions the existing proof does not reach.

## V.1 The chain in finite models (links 1 to 4)

In a finite model everything works: zeros are finitely many, the pairing is a finite sum, and "positive" means "on the line".

| # | Result | Status | Source |
|---|---|---|---|
| V.1.1 | Finite Weil criterion: zeros closed under conjugation; the zero pairing is non-negative on every finite exponential sum iff every zero is on the line | **[Lean]** | `GRH/Weil.lean`, `weil_criterion_finite` |
| V.1.2 | Zeros on the line imply the pairing is non-negative (each term is a square) | **[Lean]** | `GRH/Weil.lean`, `weilSum_re_nonneg_of_real` |
| V.1.3 | Positivity implies the line for any test class with the approximation property (a named hypothesis) | **[Lean]** | `GRH/Weil.lean`, `real_of_weilSum_nonneg` |
| V.1.4 | Weil's criterion for zeta and Dirichlet L-functions | **[classical]** | Weil 1952; Bombieri 2000 |
| V.1.5 | Weil's explicit formula for zeta holds for every smooth compactly supported test function, by the contour shift, with a polynomial zero count per unit window (Mathlib-only core, no named step) | **[Lean]** | `GRH/ContourShift.lean` (`CS.contourShift`), `GRH/ContourShiftTie.lean` (`explicit_formula_of_smooth`), `GRH/ContourShiftZeta.lean` (`zero_count_window`) |
| V.1.5b | For Dirichlet and other L-functions the explicit formula, and Weil's criterion itself, are not yet in Lean | **[open]** | `docs/unified/CONTOUR-SHIFT.md`, section 5 |
| V.1.6 | A similitude multiplying a positive form by q has all eigenvalues of modulus sqrt q | **[Lean]** | `GRH/Orbits.lean`, `similitude_eigenvalue` |
| V.1.7 | If Theta - 1/2 is skew-adjoint for a positive form, every eigenvalue has real part 1/2 (finite dimension) | **[Lean]** | `GRH/Orbits.lean`, `skew_shift_re_half` |
| V.1.8 | Lee-Yang circle theorem and Asano contraction, small cases | **[Lean]** | `GRH/LeeYang.lean`, `asano`, `ising3_zeros_on_circle` |
| V.1.9 | Fixed points of f^n are counted by points of exact period d dividing n (finite "remnants as evidence") | **[Lean]** | `GRH/Orbits.lean`, `card_fixed_pow_eq_sum` |
| V.1.10 | A finite exponential sum bounded by any exponential constant is bounded exactly ("a lossy bound becomes exact on a finite spectrum") | **[Lean]** | `GRH/Induction.lean`, `norm_le_of_exp_bound` |

## V.2 The mirror alone does not place the zeros

**V.2.1 Without positivity, duality allows off-line pairs.** An indefinite form is preserved by a mirror pair off the line (3/4 and
1/4) **[Lean]** (`GRH/Orbits.lean`, `krein_off_line`). The functional equation pairs rho with 1 - conj(rho); on the line the partner is
the zero itself, off the line it is a second zero. A mirror symmetry never places zeros on its axis by itself.

**V.2.2 The arithmetic instance.** Tate's thesis writes the completed L-function as a product of local zeta integrals, one per place,
each with its own functional equation; the global functional equation is Poisson summation for Q inside the adeles **[classical]**. On
the critical line the local factors at s and at 1 - s have the same modulus, so their ratio is a pure phase, proved in Lean for every
unramified prime **[Lean]**
(`GRH/Tate.lean`, `local_factor_unimodular`). Mathlib proves the functional equation for every even or odd function on Z/N, not only
for characters **[classical]** (in Mathlib as `completedLFunction_one_sub_even` and `completedLFunction_one_sub_odd`, `Mathlib/NumberTheory/LSeries/ZMod.lean`, Mathlib v4.34.0). Among those functions is the Davenport-Heilbronn
combination mod 5, which has a self-dual functional equation and zeros off the line **[classical]** (recalled). So local functional
equations, global Poisson and the Gaussian allow an off-line pair. This is the arithmetic `krein_off_line`.

**V.2.3 The one local sign.** What must be added is a sign. The one local sign available is Lambda(n) >= 0: each Euler factor's
log-derivative has non-negative coefficients; Davenport-Heilbronn lacks it **[classical]**. With Landau's theorem it turns a one-sided
square-root bound on psi(x) - x into a contradiction with an off-line pair **[paper]** (`grh/INDUCTION.md`, 0.2). The one-sided bound
is global: it does not follow from the local data plus Poisson, and generalised-prime systems with regular integers violate it
**[classical]** (Diamond-Montgomery-Vorhauer). This is exactly the bound the proof by others supplies.

**V.2.4 Positivity locates singularities (the bridge, II.11).** Pringsheim, Landau, Laplace and spectral instances **[Lean]**
(`Bridge/`); a positive transform has no pole of negative residue approached from the right, and the ray form excludes zeros right of
theta under a one-sided bound **[Lean]** (`Bridge/Poles.lean`, `landau_ray_poles`, `lseries_residue_nonneg`); a real zero beta in
(theta, 1) of L(chi, s) gives such a pole, of residue -m/(beta(1 - beta)) **[classical]**, two-line computation, not formalised.

**V.2.5 The two 1/2s.** Over function fields one positive duality (the Hodge index; Rosati positivity) gives both the mirror axis and
the balance point 1/2 **[classical]** (Weil 1948). In Stepanov's route and in the Lean proof by others the two 1/2s meet only in the
conclusion **[classical]** / **[external, traced]**. An arithmetic positivity in the role of the Hodge index, giving both, is
**[open]** (`bridge/BRIDGE.md`, section 4).

**V.2.6 The mirror constants.** The mirror pair Weil's form actually uses is (s = 1, s = 0); it fixes the real-place constants
(log pi + gamma, the pole terms; zeta'(0)/zeta(0) = log 2 pi) **[numerical]**. These constants belong to the archimedean part alone,
which on its own is indefinite from support 0.425 on (V.3.9). No sign comes from them (`MIRROR.md`, 0.3).

| # | Result | Status | Source |
|---|---|---|---|
| V.2.1 | Duality without positivity allows mirror pairs off the line | **[Lean]** | `GRH/Orbits.lean`, `krein_off_line` |
| V.2.2a | The ratio of the local factor at s and at 1 - s has modulus 1 on the line (unramified primes) | **[Lean]** | `GRH/Tate.lean`, `local_factor_unimodular` |
| V.2.2b | Functional equation for every even/odd function on Z/N; Davenport-Heilbronn has zeros off the line | **[classical]** (in Mathlib: `completedLFunction_one_sub_even`, `_odd`) | `grh/TATE.md`, 0.2 |
| V.2.3a | Lambda(n) >= 0 plus a one-sided square-root bound plus Landau excludes zeros right of 1/2 | **[paper]** | `grh/INDUCTION.md`, 0.2; `grh/TATE.md`, 0.3 |
| V.2.3b | The one-sided bound is global (generalised primes violate it) | **[classical]** | Diamond-Montgomery-Vorhauer; `grh/TATE.md`, 0.3 |
| V.2.4a | Positive transforms exclude negative-residue poles; ray form | **[Lean]** | `Bridge/Poles.lean`, `landau_ray_poles`, `lseries_residue_nonneg` |
| V.2.4b | A real zero in (theta, 1) gives a negative-residue pole | **[classical]** (not formalised) | `bridge/BRIDGE.md`, 1.4 |
| V.2.5a | Function fields: one positive duality gives both 1/2s | **[classical]** | Weil 1948; `bridge/BRIDGE.md`, 2.3 |
| V.2.5b | Stepanov and the Lean proof by others: the 1/2s meet only in the conclusion | **[classical]** / **[external, traced]** | `bridge/BRIDGE.md`, 2.3 and 3 |
| V.2.5c | **An arithmetic positivity giving both 1/2s** | **[open]** | `bridge/BRIDGE.md`, 4 |
| V.2.6 | The mirror pair Weil uses is (1, 0); its constants are archimedean and give no sign | **[numerical]** + **[Lean]** (via V.2.1) | `MIRROR.md`, 0.3 |

Reading: "inversion and halving": every 1/2 in these formulas is the fixed point of an inversion (s -> 1 - s, alpha -> q/alpha,
m -> x/m) **[reading]**.

## V.3 Measured: the shape of the missing positivity

On a grid of cells Weil's form is a Toeplitz matrix, because it is translation invariant. This turns the question into one about a
sequence of matrices, and numerics can probe it. Every number in this section can refute a construction; none proves a sign.

**V.3.1 The induction frame is exact.** Growing the support by one cell adds one entry, at the corner of the matrix. The bigger
section is positive exactly when that entry lands in an interval centred on the value extrapolated from all smaller scales, with the
current margin as radius (Szego recursion, Levinson) **[classical]**. Each step is one scalar condition.

**V.3.2 Each step holds, by exact cancellation.** The induction holds at every step computed, every reflection coefficient at most
0.68 in modulus, up to support a = 1.25 **[numerical]**. But the margin collapses (lambda_min about 1e-11 by a = 1.24), and the new
prime's own term is up to about 700 interval radii, of which the extrapolation from below cancels all but less than one
**[numerical]**. No estimate with slack can carry such a step: scaling one prime weight by (1 + eta) breaks positivity at eta of order
1e-3 to 1e-9 **[numerical]**.

**V.3.3 The ground state.** Minimising the form over unit vectors on each section gives the margin; the minimiser's polynomial has all
its zeros on the unit circle, which is the critical line in grid coordinates (to 1e-53), and as primes enter these zeros lock onto
zeta's (14.134725 to 3e-7 with the primes up to 11) **[numerical]**. Without the primes they are evenly spaced. The zeros of the
minimiser are on the circle for every real symmetric Toeplitz section, positive or not (Caratheodory-Fejer, Pisarenko)
**[classical]**; in Lean, `atoms_on_circle` and `atomic_toep_nonneg` (`GRH/Induction.lean`) **[Lean]**. Positivity is exactly the
statement that the uniform remnant lambda_min is non-negative.

**V.3.4 The true primes sit at the edge, not at the centre.** The margin is concave in the prime weights and the positive
configurations form a convex set **[Lean]** (`GRH/Variational.lean`, `toep_pos_convex`). Scaling the prime 2 by (1 + s) changes the
margin at rate -1.01 while the margin is 1e-9: the arithmetic configuration lies about 1e-9 from the edge of the positive window
**[numerical]**. "Positivity = stability of the minimum" holds only as a tautology **[Lean]** (`line_min_iff`, `min_at_zero_iff`).

**V.3.5 All or nothing.** At support 0.625 to 0.725 only 2 and 3 are present: A + P_2 and A + P_3 are both indefinite, A + P_2 + P_3
is positive. At every support computed beyond an entry window, the only positive set of primes is the full set present; dropping 11,
which has barely entered, already gives -1.1e-3 against +1e-9 **[numerical]**. Two combined Szego steps carry exactly the product of
the single steps, so the chain has no hidden pair certificate **[classical]**.

**V.3.6 Contraction on the sections, isometry on the space.** On the sections every step contracts (factors 1 - k^2 in (0.54, 1);
per-prime products 0.065 for 2 up to 0.92 for 11), and the product goes to zero (Kolmogorov-Szego for the atomic zero measure)
**[numerical]** + **[classical]**. A positive margin survives finitely many positive factors **[Lean]** (`GRH/Transfer.lean`,
`margin_pos_of_factors`, `prod_one_sub_le_exp`). Here the roles of Yang-Mills are reversed: eta < 1 is automatic and harmless, and the
sign is eta_p > 0 at every step.

**V.3.7 No two-term bound gives the sign.** The best bound that sees the archimedean part and the primes separately is Weyl's,
lambda_min(A) + lambda_min(sum P), attained by aligning the worst directions **[Lean]** (`two_term_bound`). It is -7.9 t_0 against a
true +1e-9 t_0 at support 1.225 **[numerical]**. The correct two-term form is Krein's extension theorem: a section is positive exactly
when Weil's distribution on the window extends to a positive measure **[classical]**.

**V.3.8 Positivity cannot be assembled place by place.** Different primes live on disjoint lattices k log p **[Lean]**
(`prime_lattices_disjoint`), so places can exchange only the lag-0 part; each prime block has zero diagonal and is indefinite as soon
as it is non-zero **[Lean]** (`zero_diag_indefinite`, `form_two_point`); so place-by-place positivity would force the real place's own
form to be positive and to pay for every prime **[Lean]** (`local_assembly_forces_arch`).

**V.3.9 The real place alone is not positive at resolvable scales.** It loses positivity at support 0.40 to 0.43, just after the prime
2 enters at (1/2) log 2 = 0.347; by support 1.225 the place-by-place condition fails by 9.7 t_0 while the whole form is positive by
1e-9 t_0 **[numerical]**. The growing mean log(r / 2 pi) confines only above frequency about 2 pi. Semilocally, Weil's form cut to a set
of places is positive only if the set holds the real place and every prime up to e^{2a} **[numerical]** (`grh/SEMILOCAL.md`).

**V.3.10 Weight positivity is not enough.** Lambda(n) >= 0, Phi(u) > 0 and the Euler product are provably insufficient; the
de Bruijn-Newman constant Lambda = 0 sits exactly at the edge **[classical]** + **[paper]** (`grh/LEE-YANG.md`, 5; Polya 1926;
Rodgers-Tao 2020).

| # | Result | Status | Source |
|---|---|---|---|
| V.3.1 | Toeplitz frame; each step is one scalar condition at the corner | **[classical]** + **[paper]** | `grh/INDUCTION.md`, 0.1 |
| V.3.2a | Each step holds up to a = 1.25, reflection coefficients at most 0.68 | **[numerical]** | `grh/INDUCTION.md`, 0.1, 0.5 |
| V.3.2b | Each step is an exact cancellation (prime term up to about 700 radii) | **[numerical]** | `grh/INDUCTION.md`, 0.1 |
| V.3.2c | Weight scaling breaks positivity at 1e-3 to 1e-9 | **[numerical]** | `grh/INDUCTION.md`, 0.3 |
| V.3.3a | Ground-state zeros on the circle, locking onto zeta's zeros | **[numerical]** | `grh/VARIATIONAL.md`, 0.1 |
| V.3.3b | Minimiser's zeros on the circle for every real symmetric Toeplitz section; positivity = remnant >= 0 | **[classical]** + **[Lean]** | `GRH/Induction.lean`, `atoms_on_circle`, `atomic_toep_nonneg`; `grh/VARIATIONAL.md`, 0.2 |
| V.3.4a | Positive configurations convex; margin concave in the weights | **[Lean]** | `GRH/Variational.lean`, `toep_pos_convex` |
| V.3.4b | The true primes sit about 1e-9 from the edge | **[numerical]** | `grh/VARIATIONAL.md`, 0.4 |
| V.3.5 | Only the full set of primes present is positive | **[numerical]** | `grh/TRANSFER.md`, 0.1 |
| V.3.6 | Per-step contraction on sections; a positive margin survives positive factors | **[numerical]** + **[Lean]** | `GRH/Transfer.lean`, `margin_pos_of_factors`, `prod_one_sub_le_exp`; `grh/TRANSFER.md`, 0.2 |
| V.3.7 | Weyl's two-term bound is the best separate bound and fails by 7.9 t_0 | **[Lean]** (bound) + **[numerical]** | `GRH/Transfer.lean`, `two_term_bound`; `grh/TRANSFER.md`, 0.3 |
| V.3.8 | Disjoint prime lattices; prime blocks indefinite; place-by-place forces the real place to pay for all | **[Lean]** | `GRH/Tate.lean`, `prime_lattices_disjoint`, `zero_diag_indefinite`, `form_two_point`, `local_assembly_forces_arch` |
| V.3.9 | Real place alone indefinite from support 0.40 to 0.43; semilocal test | **[numerical]** | `grh/TATE.md`, 0.4; `grh/SEMILOCAL.md` |
| V.3.10 | Weight positivity is not enough; Lambda = 0 at the edge | **[classical]** + **[paper]** | `grh/LEE-YANG.md`, 5 |
| V.3.11 | Explicit formula normalisation agrees to 1e-16; smallest eigenvalue on a 10-function space 2.4e-1 to 2.6e-9, no violation | **[numerical]** | `grh/weil_numerics.log`; `grh/ATTEMPT.md`, 4 |

## V.4 The open step: one missing positivity, eight faces

The missing piece: **a positive object built from the primes, the characters and the real place alone, without the zeros.** The notes
have met it eight times. Each face would close the others' consequences; they are not shown to be equivalent.

| Face | Statement | Status | Source |
|---|---|---|---|
| 1 Weil Hilbert space | A Hilbert space H_chi and a map Phi from test functions, built from arithmetic data only, with <Phi f, Phi g> = W_chi(f * g~). By Weil and GNS it exists iff GRH holds for chi. None of its subset truncations is positive (V.3.5) | **[open]** | `grh/ATTEMPT.md`, step 4 |
| 2 Critical ferromagnet | A lattice ferromagnet at its critical coupling whose block-spin law is Riemann's Phi; RH by Newman's closure. Asano adds one site at a time; here one prime at a time fails | **[open]** | `grh/LEE-YANG.md`, 5c |
| 3 Deninger space | A foliated space whose closed orbits are the primes, with a positive leafwise Hodge form. In the hyperbolic analogue positivity gives only "line or real segment"; the line needs a gap (lambda_1 >= 1/4) | **[open]** | `grh/ORBITS.md`, 6; `grh/TRANSFER.md`, 5 |
| 4 Hermite-Biehler chain | A Hermite-Biehler coupling of xi's real and imaginary parts (de Branges frame; the specific de Branges conjecture is false, Conrey-Li 2000); its Schur parameters are the step factors | **[open]**; framework **[classical]** | `grh/INDUCTION.md`, 0.4 |
| 5 Step lemma | From the primes up to p_{k+1} and the real place, put the new corner entry inside the extrapolated interval, without the zeros | **[open]** | `grh/INDUCTION.md`, 7 |
| 6 Sign of the remnant | From arithmetic alone, lambda_min(a) >= 0 at every support; equivalently the ground states converge to the zero measure | **[open]** | `grh/VARIATIONAL.md`, 0.5 |
| 7 Global sign ("it runs") | The norm in which the scaling flow runs is positive; equivalently the one-sided square-root prime bound. In the constructions where the norm is positive by construction, the space either misses the off-line zeros (Connes) or yields a half-plane (Lax-Phillips) | **[open]** | `grh/TATE.md`, 0.5, 0.6 |
| 8 All-or-nothing step | At each scale the full set of primes present, and no subset, places the corner entry inside the interval; no decomposition into pairs, single primes or two terms carries it | **[open]** | `grh/TRANSFER.md`, 5 |

Faces 2 and 3 each imply face 1 **[paper]** (`grh/INDUCTION.md`, 7; `grh/ORBITS.md`, 4). Faces 5, 6 and 8 are the same quantity read
between scales, at one scale, and over subsets **[paper]** (`grh/VARIATIONAL.md`, 5; `grh/TRANSFER.md`, 5).

**The constraint on any construction** (V.3): it cannot add one prime at a time with slack; it cannot assemble positivity place by
place or subset by subset; it cannot separate the archimedean part from the primes. All primes up to the scale and the real place must
enter together, in their exact relative position, through an exact identity.

## V.5 "It runs": the face shared with Yang-Mills

The owner named the positivity the reductio needs: "It runs." Read formally: an off-line pair of zeros would be a growing mode of the
arithmetic evolution, contradicting that the evolution does not increase a positive norm. On the completion of test functions in Weil's
form the scaling flow preserves the form automatically **[paper]**. If the flow does not increase a positive norm, there is no growing
mode; the functional equation pairs every decaying mode with a growing one; so every mode is a phase, which is RH **[Lean]**
(`GRH/Tate.lean`, `runs_and_mirror_on_line`; `atoms_on_circle` in grid form). The open part is exactly face 7: that norm is Weil's form,
and its positivity is the open step. On the constructed space the flow is an isometry (eta = 1, "flat"), and what remains are the zeros
(phases) and the orbit lengths log p: the explicit formula is a trace formula of these remnants **[classical]**.

Yang-Mills has the same formal target with the opposite missing piece (IV.8): there the positive norm is free and the margin is
missing; here the margin is not needed and the positive norm is missing **[Lean]** (`Crossover/Runs.lean`, `runs_two_targets`).

## V.6 DMP readings attached to this part (all [reading])

* **Positivity is the corollary "something exists"; forced existence lands on the prescribed line** (I.1, I.2).
* **The circle is the only self-closed existence; a collapse must split into at least two.** The ground state's zeros are always on the
  circle (V.3.3); a zero leaving the line comes with its mirror partner (V.2.1). Positivity is what keeps every zero self-paired on
  the circle.
* **The sign from the virtual flux around the true zeros.** Each prime's wobble has mean exactly zero; the real place contributes the
  growing positive mean log(r / 2 pi); the sign holds only if the mean wins against every alignment of prime phases a test function can
  resolve (by Kronecker and Voronin they can align). The margin of 1e-9 says it wins, only just (V.3.2, V.3.4).
* **The reductio as excision at G0.** An overtaking alignment would be a negative direction, that is an off-line pair; the reading says
  such an assertion is excised at once. In mathematics that needs a contradiction from arithmetic structure; duality alone gives none
  (V.2.1). The 17-million-line Lean proof by others achieved it by another route (a one-sided prime bound plus Landau).
* **The functional equation, proven to be locally evaluable** is Tate's thesis (V.2.2); it gives the mirror, not the sign.
* **GRH as the ODP's tool that runs before causality.** RH is equivalent to M(x) = O(x^{1/2 + eps}): the building blocks deviate from
  their mean density by no more than the square-root floor of independent fluctuations ("Moebius randomness") **[classical]** for the
  equivalence; reading GRH as the certificate that the blocks sit at the universal floor is interpretation.
* "What GRH is missing is its concept of the remnant of acts": face 3; "the act must entangle the real with the imaginary through a
  coupling factor": face 4; "arithmetic exists but never runs": there is no Frobenius over Z **[classical]**, and running it as content
  is face 2.

## V.7 What would close it

Any one of the eight faces, built without the zeros. The constraint from V.3 rules out every assembly with slack, by place, by
subset or by separate terms, so the construction must be an exact identity coupling all primes up to the scale and the real place. The
Yang-Mills chain (Part IV) is the model: there the positive object (e^{-S} with locality) is given by construction, and reflection
positivity follows. The open step here is to find the arithmetic G0 in which Weil positivity is a construction rather than a
conclusion (Part III).
