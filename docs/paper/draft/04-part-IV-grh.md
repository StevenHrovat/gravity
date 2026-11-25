# Part IV. The generalised Riemann hypothesis: the positivity route

*Draft 5. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/ProofPhase/`; notes relative to
`docs/rh-guide/`. Claim labels (IV.n) are listed in `../CLAIMS.md`.*

## IV.0 What is proved, by whom, and what this part does

**State of the problem.**

* The Riemann hypothesis for zeta and GRH for every Dirichlet L-function are proved in Lean by others: a library released
  2026-11-20; the Riemann hypothesis was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and the Dirichlet
  theorems are checked on the library's verification page **[external]** (`SOURCES.md`, S1 to S4; `GUIDE.md`,
  section 1). This project read the main statements in the source and did not rebuild the library.
* GRH for Dedekind, Hecke and general automorphic L-functions is not proved **[open]** (`GUIDE.md`, sections 1 and 5).
* As far as this project traced it, the proof by others does not go through Weil's positivity criterion (the positive pairing of
  II.8). Positivity enters it elsewhere: its sign is the non-negative coefficients of Landau's theorem (IV.2.3, IV.2.4). Its endgame,
  as traced here, is Landau's theorem applied to a one-sided square-root bound on the prime count, obtained from a Stepanov-type
  size balance **[external, traced, preliminary]** (`GUIDE.md`, sections 2, 4, 5).
* Tao's post of 20 November 2026 (Tao 2026) reports that L. Alpoge, the author of that library's proof, has also generated a Lean-only proof of a Generalized
  Riemann Hypothesis and, as a preliminary analysis, that its strategy appears to use the full power of modern developments in the
  Langlands program. Which L-functions that proof covers is not stated there, and how its route relates to the one traced above was
  not examined here **[external, unverified]**.

**What this part does.** It follows the other road: Weil's positivity criterion, the second column of the chain of II.8. It proves the
chain in finite models (IV.1), shows exactly why a mirror symmetry alone cannot place zeros on the line (IV.2), measures the shape of
the missing positivity (IV.3), and states the one missing construction in eight faces (IV.4), with "it runs" as the
form shared with Yang-Mills (IV.5). **This part does not prove GRH for any L-function.** Its value is a reduction that is independent of
the existing proof and would, if closed, extend to L-functions the existing proof does not reach.

## IV.1 The chain in finite models (links 1 to 4)

In a finite model everything works: zeros are finitely many, the pairing is a finite sum, and "positive" means "on the line".

| # | Result | Status | Source |
|---|---|---|---|
| II.9.3 | Finite Weil criterion: zeros closed under conjugation; the zero pairing is non-negative on every finite exponential sum iff every zero is on the line | **[Lean]** | `GRH/Weil.lean`, `weil_criterion_finite` |
| IV.1.2 | Zeros on the line imply the pairing is non-negative (each term is a square) | **[Lean]** | `GRH/Weil.lean`, `weilSum_re_nonneg_of_real` |
| IV.1.3 | Positivity implies the line for any test class with the approximation property and finite multiplicities (named hypotheses) | **[Lean]** | `GRH/Weil.lean`, `real_of_weilSum_nonneg` |
| II.9.4 | Weil's criterion for zeta and Dirichlet L-functions | **[classical]** | Weil 1952; Bombieri 2000 |
| IV.1.5 | Weil's explicit formula for zeta holds for every smooth compactly supported test function, by the contour shift, with a polynomial zero count per unit window (Mathlib-only core, no named step); the real-place term is a line integral at Re s = c > 1, and its identification with the term of Weil's closed form on the critical line is not in Lean | **[Lean]** | `GRH/ContourShift.lean` (`CS.contourShift`), `GRH/ContourShiftTie.lean` (`explicit_formula_of_smooth`), `GRH/ContourShiftZeta.lean` (`zero_count_window`) |
| IV.1.5b | For Dirichlet and other L-functions the explicit formula, and Weil's criterion itself, are classical but not yet in Lean | **[classical]** (not in Lean) | `docs/unified/CONTOUR-SHIFT.md`, section 5 |
| IV.1.6 | A similitude multiplying a positive form by q has all eigenvalues of modulus sqrt q | **[Lean]** | `GRH/Orbits.lean`, `similitude_eigenvalue` |
| IV.1.7 | If Theta - 1/2 is skew-adjoint for a positive form, every eigenvalue has real part 1/2 (finite dimension) | **[Lean]** | `GRH/Orbits.lean`, `skew_shift_re_half` |
| IV.1.8 | Lee-Yang circle theorem and Asano contraction, small cases | **[Lean]** | `GRH/LeeYang.lean`, `asano`, `ising3_zeros_on_circle` |
| IV.1.9 | Fixed points of f^n are counted by points of exact period d dividing n (finite "remnants as evidence") | **[Lean]** | `GRH/Orbits.lean`, `card_fixed_pow_eq_sum` |
| IV.1.10 | A finite exponential sum bounded by any exponential constant is bounded exactly ("a lossy bound becomes exact on a finite spectrum") | **[Lean]** | `GRH/Induction.lean`, `norm_le_of_exp_bound` |

**The explicit formula, as proved (IV.1.5).** Let c > 1, let g : R -> C be smooth with compact support, and let (gamma_i) list the
nontrivial zeros rho = 1/2 + i gamma_i of zeta with multiplicity. Write $H(s) = \int g(x)\, e^{(s - 1/2)x}\, dx$ and $\tilde g(x) = g(-x)$.
Then the sum over i of $H(\tfrac12 + i\gamma_i)$ converges, and

$$\sum_i H(\tfrac12 + i\gamma_i) = H(1) + H(0) - \sum_{n \ge 2} \frac{\Lambda(n)}{\sqrt n}\bigl(g(\log n) + g(-\log n)\bigr) + \tfrac12\bigl(A_c(g) + A_c(\tilde g)\bigr),$$

where $A_c$ is the real-place term, a line integral at Re s = c of the digamma factor against the transform of g **[Lean]**
(`GRH/ContourShiftTie.lean`, `explicit_formula_of_smooth`; `GRH/ExplicitFormula.lean`, `efRHS`). The formula is Weil's
**[classical]**; what is new is the formalisation, with no named step. That $A_c$ equals the real-place term of Weil's closed form
on the critical line is not in Lean.

**The explicit formula is one turn (IV.1.5c).** The contour shift moves the line integral of H(s) zeta'(s)/zeta(s) from Re s = c to
Re s = 1 - c, and the difference of the two lines is an integral once around the critical strip. Each zero contributes its order
times H at the zero, and the order is the winding number of one turn of the logarithmic derivative around it (II.2.7,
`full_turn_order`) **[Lean]** for the local winding, **[paper]** for reading the formula as the full turn taken once around the strip
(claim IV.1.5c).

**The certified first box, as stated.** For a = 3/5, 13/20 and 69/100 and every f in L^2(-a, a), real or complex,

$$c(a)\,\|f\|^2 \le W(f), \qquad c(\tfrac35) = 1.500\cdot 10^{-9},\quad c(\tfrac{13}{20}) = 3.398\cdot 10^{-11},\quad c(\tfrac{69}{100}) = 6.417\cdot 10^{-13},$$

where W is Weil's quadratic form of zeta on test functions supported in [-a, a]: the real place, with the constant
$-\log\pi - \gamma - \log 4a$, and the prime powers n with log n < 2a, here only 2 and 3, with weights $\Lambda(n)/\sqrt n$. The three
numbers are enclosed in ball arithmetic (`docs/unified/grh_onebox_cert-a0.60.log`, `-a0.65.log`, `-a0.69.log`; rerun with
`tools/reproduce.sh certs`) **[certified]**; the analytic estimates that make them bounds on all of L^2(-a, a) (a polynomial part
of degree below 100, a tail, and the cross term between them) are argued in `docs/unified/GRH-ONEBOX-CERT.md` **[paper]**, and the
assembly from the three inputs is **[Lean]** (`GRH/OneBoxCert.lean`, `onebox_positive`) (claim X.65).

## IV.2 The mirror alone does not place the zeros

**IV.2.1 Without positivity, duality allows off-line pairs.** An indefinite form is preserved by a mirror pair off the line (3/4 and
1/4) **[Lean]** (`GRH/Orbits.lean`, `krein_off_line`). The functional equation pairs rho with 1 - conj(rho); on the line the partner is
the zero itself, off the line it is a second zero. A mirror symmetry never places zeros on its axis by itself.

**IV.2.2 The arithmetic instance.** Tate's thesis writes the completed L-function as a product of local zeta integrals, one per place,
each with its own functional equation; the global functional equation is Poisson summation for Q inside the adeles **[classical]**. On
the critical line the local factors at s and at 1 - s have the same modulus, so their ratio is a pure phase, proved in Lean for every
unramified prime **[Lean]**
(`GRH/Tate.lean`, `local_factor_unimodular`). Mathlib proves the functional equation for every even or odd function on Z/N, not only
for characters **[classical]** (in Mathlib as `completedLFunction_one_sub_even` and `completedLFunction_one_sub_odd`, `Mathlib/NumberTheory/LSeries/ZMod.lean`, Mathlib v4.34.0). Among those functions is the Davenport-Heilbronn
combination mod 5, which has a self-dual functional equation and zeros off the line **[classical]** (recalled). So local functional
equations, global Poisson and the Gaussian allow an off-line pair. This is the arithmetic `krein_off_line`.

**IV.2.3 The one local sign.** What must be added is a sign. The one local sign available is Lambda(n) >= 0: each Euler factor's
log-derivative has non-negative coefficients; Davenport-Heilbronn lacks it **[classical]**. With Landau's theorem it turns a one-sided
square-root bound on psi(x) - x into a contradiction with an off-line pair **[paper]** (`grh/INDUCTION.md`, 0.2). The one-sided bound
is global: it does not follow from the local data plus Poisson, and generalised-prime systems with regular integers violate it
**[classical]** (Diamond-Montgomery-Vorhauer). This is exactly the bound the proof by others supplies.

**IV.2.4 Positivity locates singularities (the bridge, II.11).** Pringsheim, Landau, Laplace and spectral instances **[Lean]**
(`Bridge/`); a positive transform has no pole of negative residue approached from the right, and the ray form excludes poles of non-positive residue
right of theta **[Lean]** (`Bridge/Poles.lean`, `landau_ray_poles`, `lseries_residue_nonneg`); a real zero beta in (theta, 1) of
L(chi, s) gives such a pole, of residue -m/(beta(1 - beta)) **[classical]**, two-line computation, not formalised, and this step is what
turns the Lean statement into one about zeros.

**IV.2.5 The two 1/2s.** Over function fields one positive duality (the Hodge index; Rosati positivity) gives both the mirror axis and
the balance point 1/2 **[classical]** (Weil 1948: the two books of 1948) **[reading]** for the phrase "gives both". In Stepanov's route and in the Lean proof by others the two 1/2s meet only in the
conclusion **[reading]** (from `GUIDE.md`; the mirror step in the Lean is **[external, traced]**). An arithmetic positivity in the role of the Hodge index, giving both, is
**[open]** (`bridge/BRIDGE.md`, section 4).

**IV.2.6 The mirror constants.** The mirror pair Weil's form actually uses is (s = 1, s = 0); it fixes the real-place constants
(log pi + gamma, the pole terms; zeta'(0)/zeta(0) = log 2 pi) **[classical]**; the measured effect on the form is **[numerical]**. These constants belong to the archimedean part alone,
which on its own is indefinite from support 0.425 on (IV.3.9; the smallest eigenvalue of the archimedean part turns negative between 0.40 and 0.425). No sign comes from them (`MIRROR.md`, 0.3).

| # | Result | Status | Source |
|---|---|---|---|
| IV.2.1 | Duality without positivity allows mirror pairs off the line | **[Lean]** | `GRH/Orbits.lean`, `krein_off_line` |
| IV.2.2a | The ratio of the local factor at s and at 1 - s has modulus 1 on the line (unramified primes) | **[Lean]** | `GRH/Tate.lean`, `local_factor_unimodular` |
| IV.2.2b | Functional equation for every even/odd function on Z/N; Davenport-Heilbronn has zeros off the line | **[classical]** (in Mathlib: `completedLFunction_one_sub_even`, `_odd`) | `grh/TATE.md`, 0.2 |
| IV.2.3a | Lambda(n) >= 0 plus a one-sided square-root bound plus Landau excludes zeros right of 1/2 | **[paper]** | `grh/INDUCTION.md`, 0.2; `grh/TATE.md`, 0.3 |
| IV.2.3b | The one-sided bound is global (generalised primes violate it) | **[classical]** | Diamond-Montgomery-Vorhauer; `grh/TATE.md`, 0.3 |
| IV.2.4a | Positive transforms exclude negative-residue poles; ray form | **[Lean]** | `Bridge/Poles.lean`, `landau_ray_poles`, `lseries_residue_nonneg` |
| IV.2.4b | A real zero in (theta, 1) gives a negative-residue pole | **[classical]** (not formalised) | `bridge/BRIDGE.md`, 1.4 |
| IV.2.5a | Function fields: one positive duality gives both 1/2s | **[classical]** | Weil 1948; `bridge/BRIDGE.md`, 2.3 |
| IV.2.5b | Stepanov and the Lean proof by others: the 1/2s meet only in the conclusion | **[reading]** (the mirror step: **[external, traced]**) | `bridge/BRIDGE.md`, 2.3 and 3 |
| IV.2.5c | **An arithmetic positivity giving both 1/2s** | **[open]** | `bridge/BRIDGE.md`, 4 |
| IV.2.6 | The mirror pair Weil uses is (1, 0); its constants are archimedean and give no sign | **[numerical]** + **[Lean]** (via IV.2.1) | `MIRROR.md`, 0.3 |

Reading: "inversion and halving": every 1/2 in these formulas is the fixed point of an inversion (s -> 1 - s, alpha -> q/alpha,
m -> x/m) **[reading]**.

## IV.3 Measured: the shape of the missing positivity

On a grid of cells Weil's form is a Toeplitz matrix, because it is translation invariant. This turns the question into one about a
sequence of matrices, and numerics can probe it. Every number in this section can refute a construction; none proves a sign. Margins depend on the discretisation: unless stated, cells are
the C^1 spline cells (r = 3) with smoothing eps = 0.05; at eps = 0.025 the margin at support 1.2 is 1e-11 instead of 1e-9, and on the step-cell grid (r = 1) it is 8e-4.
As in IV.1, the support a is the half-width of the test function's support, so the primes p with log p <= 2a enter (2 and 3 up
to a = log 4 / 2 = 0.69). The margins here are smallest eigenvalues of the smoothed form on a finite grid of cells: a minimum over a
subspace is at least the minimum over the whole space, so these numbers lie above the true margin. They are not comparable with
the certified lower bounds of IV.1, and they do not contradict the upper bound of about 3.6e-15 at a = 0.75 found with a trial
function (X.4.4) **[paper]**.

**IV.3.1 The induction frame is exact.** Growing the support by one cell adds one entry, at the corner of the matrix. The bigger
section is positive exactly when that entry lands in an interval centred on the value extrapolated from all smaller scales, with the
current margin as radius (Szego recursion, Levinson) **[classical]**. Each step is one scalar condition.

**IV.3.2 Each step holds, by exact cancellation.** The induction holds at every step computed, every reflection coefficient at most
0.68 in modulus, up to support a = 1.25 **[numerical]**. But the margin collapses (lambda_min about 1e-11 by a = 1.24 at eps = 0.025), and the new
prime's own term is up to about 700 interval radii, of which the extrapolation from below cancels all but less than one
**[numerical]**. No estimate with slack can carry such a step: scaling one prime weight by (1 + eta) breaks positivity at eta of order
1e-3 to 1e-9 **[numerical]**.

**IV.3.3 The ground state.** Minimising the form over unit vectors on each section gives the margin; the minimiser's polynomial has all
its zeros on the unit circle, which is the critical line in grid coordinates (to 1e-53), and as primes enter these zeros lock onto
zeta's (14.134725 to 3e-7 with the primes up to 11) **[numerical]**. Without the primes they are evenly spaced. The zeros
of the minimiser are on the circle for every real symmetric Toeplitz section, positive or not (Caratheodory-Fejer; Pisarenko 1973; Makhoul 1981)
**[classical]**. In Lean is the Caratheodory-Toeplitz equivalence for atomic measures: if every section is positive
the atoms lie on the circle (`atoms_on_circle`), and atoms on the circle with non-negative weights give positive sections
(`atomic_toep_nonneg`, `GRH/Induction.lean`) **[Lean]**. Positivity is exactly the
statement that the uniform remnant lambda_min is non-negative.

**IV.3.4 The true primes sit at the edge, not at the centre.** The margin is concave in the prime weights (a minimum of linear
forms, **[paper]**) and the positive configurations form a convex set **[Lean]** (`GRH/Variational.lean`, `toep_pos_convex`). Scaling the prime 2 by (1 + s) changes the
margin at rate -1.01 while the margin is 1e-9: the arithmetic configuration lies about 1e-9 from the edge of the positive window
**[numerical]**. "Positivity = stability of the minimum" holds only as a tautology **[Lean]** (`line_min_iff`, `min_at_zero_iff`).

**IV.3.5 All or nothing.** At support 0.625 to 0.725 only 2 and 3 are present: A + P_2 and A + P_3 are both indefinite, A + P_2 + P_3
is positive. At every support computed beyond an entry window, the only positive set of primes is the full set present; dropping 11,
which has barely entered, already gives -1.1e-3 against +1e-9 **[numerical]**. Two combined Szego steps carry exactly the product of
the single steps, so the chain has no hidden pair certificate **[paper]** (the composition of Szego steps is **[classical]**).

**IV.3.6 Contraction on the sections, isometry on the space.** On the sections every step contracts (factors 1 - k^2 in (0.54, 1);
per-prime products 0.065 for 2 up to 0.92 for 11), and the product goes to zero (Kolmogorov-Szego for the atomic zero measure)
**[numerical]** + **[classical]**. A positive margin survives finitely many positive factors **[Lean]** (`GRH/Transfer.lean`,
`margin_pos_of_factors`; with a uniform factor bound q < 1, `survive`, `survive_pos` in `Unified/Ledger.lean`), and
`prod_one_sub_le_exp` bounds the product above by exp(-sum of the contractions) **[Lean]**. Here the roles of Yang-Mills are reversed: eta < 1 is automatic and harmless, and the
sign is eta_p > 0 at every step.

**IV.3.7 No two-term bound gives the sign.** The best bound that sees the archimedean part and the primes separately is Weyl's,
lambda_min(A) + lambda_min(sum P), attained by aligning the worst directions **[paper]**; the inequality itself is **[Lean]**
(`two_term_bound`). It is -7.9 t_0 against a
true +1e-9 t_0 at support 1.225 **[numerical]**. The correct two-term form is Krein's extension theorem: a section is positive exactly
when Weil's distribution on the window extends to a positive measure **[classical]**.

**IV.3.8 Positivity cannot be assembled place by place.** Different primes live on disjoint lattices k log p **[Lean]**
(`prime_lattices_disjoint`), so places can exchange only the lag-0 part; each prime block has zero diagonal and is indefinite as soon
as it is non-zero **[Lean]** (`zero_diag_indefinite`, `form_two_point`); so place-by-place positivity would force the real place's own
form to be positive and to pay for every prime **[Lean]** (`local_assembly_forces_arch`).

**IV.3.9 The real place alone is not positive at resolvable scales.** It loses positivity at support 0.40 to 0.43, just after the prime
2 enters at (1/2) log 2 = 0.347; by support 1.225 the place-by-place condition fails by 9.7 t_0 while the whole form is positive by
1e-9 t_0 **[numerical]**. The growing mean log(r / 2 pi) confines only above frequency about 2 pi. Semilocally, Weil's form cut to a set
of places is positive only if the set holds the real place and every prime up to e^{2a} **[numerical]** (`grh/SEMILOCAL.md`).

**IV.3.10 Weight positivity is not enough.** Lambda(n) >= 0, Phi(u) > 0 and the Euler product are provably insufficient; the
de Bruijn-Newman constant Lambda = 0 sits exactly at the edge (Lambda >= 0 is Rodgers-Tao **[classical]**; Lambda <= 0 is RH, so it holds
through IV.0a **[external]**) **[paper]** (`grh/LEE-YANG.md`, 5; Polya 1926;
Rodgers-Tao 2020).

| # | Result | Status | Source |
|---|---|---|---|
| IV.3.1 | Toeplitz frame; each step is one scalar condition at the corner | **[classical]** + **[paper]** | `grh/INDUCTION.md`, 0.1 |
| IV.3.2a | Each step holds up to a = 1.25, reflection coefficients at most 0.68 | **[numerical]** | `grh/INDUCTION.md`, 0.1, 0.5 |
| IV.3.2b | Each step is an exact cancellation (prime term up to about 700 radii) | **[numerical]** | `grh/INDUCTION.md`, 0.1 |
| IV.3.2c | Weight scaling breaks positivity at 1e-3 to 1e-9 | **[numerical]** | `grh/INDUCTION.md`, 0.3 |
| IV.3.3a | Ground-state zeros on the circle, locking onto zeta's zeros | **[numerical]** | `grh/VARIATIONAL.md`, 0.1 |
| IV.3.3b | Minimiser's zeros on the circle for every real symmetric Toeplitz section; positivity = remnant >= 0 | **[classical]** + **[Lean]** | `GRH/Induction.lean`, `atoms_on_circle`, `atomic_toep_nonneg`; `grh/VARIATIONAL.md`, 0.2 |
| IV.3.4a | Positive configurations convex **[Lean]**; margin concave in the weights **[paper]** | **[Lean]** | `GRH/Variational.lean`, `toep_pos_convex` |
| IV.3.4b | The true primes sit about 1e-9 from the edge | **[numerical]** | `grh/VARIATIONAL.md`, 0.4 |
| IV.3.5 | Only the full set of primes present is positive | **[numerical]** | `grh/TRANSFER.md`, 0.1 |
| IV.3.6a, IV.3.6b | Per-step contraction on sections; a positive margin survives positive factors | **[numerical]** + **[Lean]** | `GRH/Transfer.lean`, `margin_pos_of_factors`, `prod_one_sub_le_exp`; `grh/TRANSFER.md`, 0.2 |
| IV.3.7a, IV.3.7b | Weyl's two-term inequality **[Lean]**; best separate bound **[paper]**; fails by 7.9 t_0 | **[Lean]** (inequality) + **[paper]** + **[numerical]** | `GRH/Transfer.lean`, `two_term_bound`; `grh/TRANSFER.md`, 0.3 |
| IV.3.8 | Disjoint prime lattices; prime blocks indefinite; place-by-place forces the real place to pay for all | **[Lean]** | `GRH/Tate.lean`, `prime_lattices_disjoint`, `zero_diag_indefinite`, `form_two_point`, `local_assembly_forces_arch` |
| IV.3.9 | Real place alone indefinite from support 0.40 to 0.43; semilocal test | **[numerical]** | `grh/TATE.md`, 0.4; `grh/SEMILOCAL.md` |
| IV.3.10 | Weight positivity is not enough; Lambda = 0 at the edge (Lambda <= 0 through IV.0a) | **[classical]** + **[external]** + **[paper]** | `grh/LEE-YANG.md`, 5 |
| IV.3.11 | Explicit formula normalisation agrees to about 1e-15; smallest eigenvalue on a 10-function space 2.4e-1 to 2.6e-9 up to support 0.7 (noise level beyond 1.0), no violation | **[numerical]** | `grh/weil_numerics.log`; `grh/ATTEMPT.md`, 4 |

## IV.4 The open step: one missing positivity, eight faces

The missing piece: **a positive object built from the primes, the characters and the real place alone, without the zeros.** For
zeta and the Dirichlet L-functions the positivity itself now follows from the external theorem and Weil's criterion (II.9); what
stays open there is a proof from arithmetic alone, and beyond Dirichlet the statement itself, for which no card is written yet
(IV.1.5b). The step asks for non-negativity at every support, not for a margin uniform in the support, which is false for zeta's
zero measure (X.45b). The notes have met it eight times. Each face, if built, would give the open step; the relations proved among the faces are the two
stated below the table.

| Face | Statement | Status | Source |
|---|---|---|---|
| 1 Weil Hilbert space | A Hilbert space H_chi and a map Phi from test functions, built from arithmetic data only, with <Phi f, Phi g> = W_chi(f * g~). By Weil and GNS it exists iff GRH holds for chi. None of its subset truncations is positive (IV.3.5) | **[open]** | `grh/ATTEMPT.md`, step 4 |
| 2 Critical ferromagnet | A lattice ferromagnet at its critical coupling whose block-spin law is Riemann's Phi; RH by Newman's closure. Asano adds one site at a time; here one prime at a time fails | **[open]** | `grh/LEE-YANG.md`, 5c |
| 3 Deninger space | A foliated space whose closed orbits are the primes, with a positive leafwise Hodge form. In the hyperbolic analogue positivity gives only "line or real segment"; the line needs a gap (lambda_1 >= 1/4) | **[open]** | `grh/ORBITS.md`, 6; `grh/TRANSFER.md`, 5 |
| 4 Hermite-Biehler chain | A Hermite-Biehler coupling of xi's real and imaginary parts (de Branges frame; Conrey and Li 2000 examine de Branges' positivity conditions and indicate their difficulty; that a stated condition fails is recalled, not checked here); its Schur parameters are the step factors | **[open]**; framework **[classical]** | `grh/INDUCTION.md`, 0.4 |
| 5 Step lemma | From the primes up to p_{k+1} and the real place, put the new corner entry inside the extrapolated interval, without the zeros | **[open]** | `grh/INDUCTION.md`, 7 |
| 6 Sign of the remnant | From arithmetic alone, lambda_min(a) >= 0 at every support; equivalently the ground states converge to the zero measure | **[open]** | `grh/VARIATIONAL.md`, 0.5 |
| 7 Global sign ("it runs") | The norm in which the scaling flow runs is positive; equivalently the one-sided square-root prime bound. In the constructions where the norm is positive by construction, the space either misses the off-line zeros (Connes) or yields a half-plane (Lax-Phillips) (recalled, not traced to a page) | **[open]** | `grh/TATE.md`, 0.5, 0.6 |
| 8 All-or-nothing step | At each scale the full set of primes present, and no subset, places the corner entry inside the interval; no decomposition into pairs, single primes or two terms carries it | **[open]** | `grh/TRANSFER.md`, 5 |

Faces 2 and 3 each imply face 1 **[paper]** (`grh/INDUCTION.md`, 7; `grh/ORBITS.md`, 4). Faces 5, 6 and 8 are the same quantity read
between scales, at one scale, and over subsets **[paper]** (`grh/VARIATIONAL.md`, 5; `grh/TRANSFER.md`, 5).

**The constraint on any construction** (IV.3): it cannot add one prime at a time with slack; it cannot assemble positivity place by
place or subset by subset; it cannot separate the archimedean part from the primes. All primes up to the scale and the real place must
enter together, in their exact relative position, through an exact identity.

## IV.5 "It runs": the face shared with Yang-Mills

The first author named the positivity the reductio needs: "It runs." Read formally: an off-line pair of zeros would be a growing mode of the
arithmetic evolution, contradicting that the evolution does not increase a positive norm. On the completion of test functions in Weil's
form the scaling flow preserves the form automatically **[paper]**. If the flow does not increase a positive norm, there is no growing
mode; the functional equation pairs every decaying mode with a growing one; so every mode is a phase, which is RH. The abstract implication (a contraction with a mirror pair of modes has modulus one) is **[Lean]**
(`GRH/Tate.lean`, `runs_and_mirror_on_line`; `atoms_on_circle` in grid form); that the modes are the zeros and that the flow is a
contraction in Weil's norm is **[open]** (face 7). The open part is exactly face 7: that norm is Weil's form,
and its positivity is the open step. On the constructed space the flow is an isometry (eta = 1, "flat"), and what remains are the zeros
(phases) and the orbit lengths log p: the explicit formula is a trace formula of these remnants **[classical]**.

Yang-Mills has the same formal target with the opposite missing piece (III.8): there the positive norm is free and the margin is
missing; here the margin is not needed and the positive norm is missing **[paper]**; the Lean states the two targets (`Crossover/Runs.lean`, `runs_two_targets`: modulus one, and
exclusion of a strictly contracted set) **[Lean]**.

## IV.6 DMP readings attached to this part (all [reading])

* **Positivity is the corollary "something exists"; forced existence lands on the prescribed line** (I.1, I.2).
* **The circle is the only self-closed existence; a collapse must split into at least two.** The ground state's zeros are always on the
  circle (IV.3.3); a zero leaving the line comes with its mirror partner (IV.2.1). Positivity is what keeps every zero self-paired on
  the circle.
* **The sign from the virtual flux around the true zeros.** Each prime's wobble has mean exactly zero; the real place contributes the
  growing positive mean log(r / 2 pi); the sign holds only if the mean wins against every alignment of prime phases a test function can
  resolve (by Kronecker and Voronin they can align). The margin of 1e-9 says it wins, only just (IV.3.2, IV.3.4).
* **The reductio as excision at G0.** An overtaking alignment would be a negative direction, that is an off-line pair; the reading says
  such an assertion is excised at once. In mathematics that needs a contradiction from arithmetic structure; duality alone gives none
  (IV.2.1). The 17-million-line Lean proof by others achieved it by another route (a one-sided prime bound plus Landau).
* **That the functional equation can be evaluated place by place** is Tate's thesis (IV.2.2); it gives the mirror, not the sign.
* **GRH as the ODP's tool that runs before causality.** RH is equivalent to M(x) = O(x^{1/2 + eps}): the building blocks deviate from
  their mean density by no more than the square-root floor of independent fluctuations ("Moebius randomness") **[classical]** for the
  equivalence; reading GRH as the certificate that the blocks sit at the universal floor is interpretation.
* "What GRH is missing is its concept of the remnant of acts": face 3; "the act must entangle the real with the imaginary through a
  coupling factor": face 4; "arithmetic exists but never runs": there is no Frobenius over Z **[classical]**, and running it as content
  is face 2.

## IV.7 What would close it

Any one of the eight faces, built without the zeros. The constraint from IV.3 rules out every assembly with slack, by place, by
subset or by separate terms, so the construction must be an exact identity coupling all primes up to the scale and the real place. The
Yang-Mills chain (Part III) is the model: there the positive object (e^{-S} with locality) is given by construction, and reflection
positivity follows. The open step here is to find the arithmetic G0 in which Weil positivity is a construction rather than a
conclusion (Part X).

## IV.8 The box in the one-box test

**Gate factor and marker.** The ticks are the scales, each carrying the margin to the next. The first author reads each scale as one, and so
as existence itself **[reading]**. At each scale the gate reads inside when the margin is carried to the next
scale with a nonnegative factor, the sign at that scale; the marker is the claim "inside". The box of a finite zero model passes
exactly when the sign holds at every scale, the card's open step (`ScaleSign`) **[Lean]** (`grh_box_iff`, `ETM/CardBox.lean`; claim IV.8a). For a
model of zeta's zeros with nonnegative weights it passes under Mathlib's statement of the Riemann hypothesis, taken as a named
`External` slot **[Lean]** (`grh_box_of_RH`). The first ticks are certified: at the start {infinity, 2, 3} the sign holds with
explicit margins (X.65, **[certified]** for the enclosures, **[paper]** for the analytic estimates). Small supports have a
literature: Yoshida studied the Hermitian forms of the explicit formula, and Connes and Consani proved Weil positivity for test
functions supported so close to 1 that only the real place enters **[external, recalled]**; the certified first box is the next
range, where the primes 2 and 3 enter, with explicit margins. Like every card box it is a restatement of the open step (II.5) **[paper]**. Its open ticks are the scales beyond the start (IV.4).
