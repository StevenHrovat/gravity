# A scale-by-scale positivity induction over the primes

Private working note, 2026-11-23. It follows `ATTEMPT.md` (step 4), `SEMILOCAL.md`, `LEE-YANG.md` and `ORBITS.md`.
The question comes from the owner's framing (PREP.md, "GRH from the other side"), and the round was approved by the
owner. The task: build Weil positivity up scale by scale, the way M1 builds its effective actions up scale by scale.
Each step carries positivity from the support where the primes up to p_k act to the support where p_{k+1} enters.

As in `LEE-YANG.md` section 0, RH and Dirichlet GRH are proved (Lean), so every positivity below is true. The open
question is whether an induction over the primes proves it **independently**, from arithmetic alone.

**Claim marks** are as in `ATTEMPT.md`:
- **[numerical]** = computed by `induction.py` (output `induction.log`; its part 0 checks the functional against the
  zeros to 1e-61);
- **[classical]** = known; items recalled from the literature rather than re-read in this session say "recalled";
- **[proved here]** = argued in this note, on paper unless it says Lean;
- **[Lean]** = `ProofPhase/GRH/Induction.lean`, 5 theorems, standard axioms only (`axioms-induction.log`);
- **[reading]** = interpretation;
- **[open]** = not settled.

---

## 0. The answers

1. **The induction frame is exact, and each step is a single scalar condition.** On a grid of cells, Weil's form is
   a Toeplitz matrix, because the form is translation invariant. Growing the support by one cell adds one new entry,
   at the matrix corner. The bigger section is positive exactly when that entry lands in an interval: its centre is
   the value extrapolated from all smaller scales, and its radius is the current margin E (Szego recursion,
   Levinson). The induction holds numerically at every step computed, with room: every reflection coefficient has
   |k| <= 0.68. But the margin itself collapses (lambda_min about 1e-11 by a = 1.24). The new prime's own term is up
   to about 700 interval radii, and the extrapolation from below cancels all but less than one of them. Each step is
   that cancellation **[numerical]**; **[classical]** for the recursion.
   In scaling form (section 1a), each step must extend the scaling action as a unitary on the constructed Hilbert
   space. Scale invariance makes it isometric for free; being unitary on a Hilbert space is exactly positivity, so
   this is the same target, stated cleanly.
2. **The dichotomy splits Weil's form into a boundary part and a bulk part.** The boundary part is exactly the prime
   side, the other proof's object.
   - **The boundary part:** when p_{k+1} enters, its term couples only the two ends of the support, so it is purely
     a boundary term. It is not small: as an operator its norm is log p / sqrt p however thin the band.
   - **What the boundary part equals:** positivity on two-bump test functions is **equivalent** to a two-sided bound
     on the smoothed (psi(x) - x)/sqrt(x), the square-root prime count. Through Landau's theorem, even a one-sided
     version with sub-exponential loss excludes every zero right of 1/2 **[proved here]**, on paper.
   - **The two proofs:** the other proof establishes the boundary statement (Stepanov plus Arakelov), and the
     positivity route asks for the bulk.
3. **The integer quantum is used, but on the other side.** Three findings:
   - **[Lean] Finite spectrum:** a lossy bound with any constant becomes exact.
   - **Over the integers:** Landau's theorem plays this role. The integer multiplicity enters through Stepanov's
     balance x/m + m in the other proof.
   - **[numerical] On the positivity side:** the prime weights must be exact to about the margin (relative
     1e-9 for p = 2 at a = 1.25), so continuous estimates cannot carry the step. But exact integer weights alone do
     not give positivity; the Euler product's positive weights were shown insufficient three times before.
4. **The owner's coupling is precisely the de Branges / Krein frame, but a prime is not a chain step.**
   - **The chain:** positivity at every scale is a chain of nested Hilbert spaces of entire functions, in discrete
     form the Szego recursion with reflection coefficients in the unit disk. "The chain stays Hermite-Biehler" is a
     correct restatement **[classical]** (recalled).
   - **Where primes sit:** the chain parameter is the scale. Primes are where the moments receive impulses, and
     every scale step needs the condition, not only prime steps. Coefficients at prime lags look like the others
     (mean |k| 0.25 against 0.20) **[numerical]**.
   - **Conrey and Li:** their counterexample refutes de Branges's specific positivity (a fixed Gamma-factor space with
     a zeta multiplier), not this chain. But this chain's step condition is RH-equivalent scale by scale, and no rule
     produces it from arithmetic.
5. **Numerics (CPU, under a minute):**
   - **The margin:** lambda_min of the section falls by a factor of 0.06 when 2 enters and 0.009 when 3 enters. Later
     factors are 0.27 to 0.67 per prime power.
   - **Dropping the entering prime:** lambda_min turns clearly negative (-0.08 to -0.73 of t_0) within 0.014 to 0.041
     of (1/2) log p, the sharper analogue of `SEMILOCAL.md`.

**Where it stops (section 7):** at the step lemma, a rule that, from the primes up to p_{k+1} and the real place,
puts the new corner entry inside the extrapolated interval (equivalently, bounds the margin's drop across a step from
below by a positive factor) without using the zeros. Each of the four earlier forms would supply it, and it is the
same obstacle sliced by scale.

---

## 1. The frame

**Weil's form at support a.** In the conventions of `weil_numerics.py`, `SEMILOCAL.md` section 1, real f supported in
[-a, a], h = f * f~:

  W(f) = E(h),  E(h) = POLE + REAL - sum_n Lambda(n) n^{-1/2} [h(log n) + h(-log n)],
  POLE = int h(u) 2 cosh(u/2) du,  REAL = -(log pi + gamma) h(0) + int_0^inf [e^{-2u} h(0) - e^{-u/2} h(u)] 2/(1-e^{-2u}) du.

The REAL term is the Gamma-factor term of `SEMILOCAL.md`, rewritten from the frequency variable into u through the
integral representation of the digamma function. `induction.py` part 0 checks this E against the zero side
sum_gamma h^(gamma) for two Gaussians h, to 1e-61 **[numerical]**.

**P(k).** Let p_1 < p_2 < ... be the primes and a_k = (1/2) log p_{k+1}. P(k) says that W >= 0 on
L^2[-a_k, a_k]. On that support, only the prime powers n < p_{k+1} enter (h vanishes beyond 2a = log p_{k+1}), so the full form
and the semilocal form with all primes up to p_k agree there exactly (`SEMILOCAL.md` answer 3) **[proved here]**.
- **P(0)** is positivity of the archimedean form for |x| <= (1/2) log 2. Yoshida proved positivity for small supports;
  Connes and Consani proved it up to this support (2021) **[classical]** (recalled).
- **Monotone margin:** the margin lambda(a) = inf W(f)/||f||^2 over L^2[-a, a] is non-increasing in a (the spaces are
  nested). So P(k+1) implies P(k), and the induction runs in the hard direction **[proved here]**, trivial.
- **The margin collapses:** lambda(a) -> 0 at least exponentially. Time-limited functions can concentrate their
  frequencies in the zero-free gap |r| < 14.13 up to a leakage of about e^{-2 a 14.13} (Slepian concentration), and the
  zero side sum_gamma |F(gamma)|^2 sees only that leakage **[proved here]**, sketch.
- **The step must be multiplicative:** a step estimate of the form lambda(a + delta) >= lambda(a) - C delta must fail,
  and the step must be a relative one, lambda(a + delta) >= (1 - kappa delta) lambda(a) **[proved here]**.

**The grid version: Toeplitz and Szego.** Take cells b = 1_[0,eps] convolved r times (r = 1 step functions; r = 3
C^1 splines), translated by multiples of eps. The form on N cells is the Toeplitz matrix T_N = (t_{|i-j|}), with
t_m = E(e_m), where e_m is the centred B-spline of order 2r moved to +-m eps and symmetrised. This holds because the
form is translation invariant **[proved here]**. Then **[classical]** (Szego recursion, Levinson-Durbin):

  T_{N+1} > 0  iff  T_N > 0 and |k_N| < 1,  k_N = -(t_N - t^_N) / E_{N-1},  E_N = E_{N-1} (1 - k_N^2),

where t^_N is the value of t_N extrapolated linearly from t_0..t_{N-1} (the centre of the set of positive extensions),
and E_{N-1} is the prediction error, the radius of that set. **The induction step is one scalar condition: the new
corner entry must land within E_{N-1} of the extrapolation.**

**The moments are the zero measure.** By the explicit formula,

  t_m = sum over zeros rho = 1/2 + i t_rho of w_rho z_rho^m,  z_rho = e^{i eps t_rho},  w_rho = |b^(t_rho)|^2 on the line.

So the Toeplitz sections are the moment matrices of the zeros wrapped onto the unit circle:
- a zero on the line is an atom on the circle with weight >= 0;
- a zero off the line, at Re rho = 1/2 + beta, is an atom at radius e^{eps beta};
- the functional equation's mirror rho -> 1 - conj rho is z -> (conj z)^{-1}.

This is why positivity forces the line. The finite-atom version is proved in Lean:
- positive atoms on the circle give positive sections (`atomic_toep_nonneg`);
- positive sections bound the moments (`toep_moment_bound`);
- bounded moments of finitely many atoms put them inside the closed disk (`atoms_inside_circle`, via item 3's
  `norm_le_of_exp_bound`);
- with the mirror, on the circle (`atoms_on_circle`) **[Lean]**.

For zeta, positivity for every grid (every eps) is Weil positivity, because step functions are dense in the relevant
Sobolev norm, and so it is RH **[proved here]**, on paper, with Weil's criterion **[classical]**. Whether a single fixed
grid suffices is **[open]**: wrapping the zeros onto the circle makes the atoms accumulate, and the finite argument does
not transfer directly.

## 1a. The target in scaling form: each step keeps the scaling action unitary

This section answers the coordinator's mapping of the owner's "scale invariant, flat curvature".

**Flat scaling characters are the critical line [classical].** Let the multiplicative group R_+ act on
L^2(R_+, dx) by (U_lambda f)(x) = lambda^{1/2} f(lambda x). This action is unitary, and dx/x is the group's Haar
measure. The characters x^{-s} are its generalised eigenfunctions, with eigenvalue lambda^{1/2 - s}. That eigenvalue
has modulus 1 for every lambda, the "flat" case, exactly when Re s = 1/2. This is Mellin-Plancherel, and the same
picture as Connes's scaling action.

In the variable u = log x used throughout, scaling is translation, f(x) = x^{-1/2} phi(log x) turns L^2(dx) into
L^2(du), and a zero rho = 1/2 + beta + i gamma corresponds to the character e^{(beta + i gamma) u}:
- **On the line:** beta = 0 and the character is flat.
- **Off the line:** it grows or decays like e^{beta u}. On the grid of section 1 this is an atom at radius e^{eps beta}
  instead of on the unit circle.

**The induction target in this form [proved here], with [classical] operator theory.** Build the space H_a from
Weil's form on L^2[-a, a]: complete, after dividing out null vectors. Translation by t is defined on the functions
supported in [-a, a - t] and maps them to [-a + t, a].
1. **Isometric for free.** W is translation invariant, so W(f(. - t)) = W(f). The scaling action preserves the form
   at every scale, whatever its sign. This is the scale invariance, and it is exact. On the grid it is the Toeplitz
   structure: the shift by one cell preserves the form.
2. **Unitary only with positivity.** If W >= 0 on [-a, a], H_a is a Hilbert space and the translations are partial
   isometries in the ordinary sense. As a grows they become a unitary group, whose spectrum is a set of flat
   characters: Re s = 1/2. If W is indefinite, the translations are isometries of an indefinite (Krein) space. There
   the generator can have mirror pairs off the line, as in the explicit example `krein_off_line` of `ORBITS.md`
   (eigenvalues 3/4 and 1/4 for a form that is preserved exactly). In the finite grid model, positive sections plus
   the mirror force every atom onto the circle (`atoms_on_circle` **[Lean]**): unitary scaling.
3. **One step is one unitary extension.** On N positive cells, the shift is a partial isometry from the first N - 1
   cells onto the last N - 1. Adding a cell extends it to an isometry of a Hilbert space with one more dimension
   exactly when the new corner entry lies in the extrapolated interval, that is |k_N| < 1. The reflection
   coefficient is the parameter of that extension (Szego recursion; the same coefficients drive the unitary CMV
   model of the shift) **[classical]**.

So the cleanest form of the target is this: **each step extends the scaling action as an isometry of a positive
(Hilbert) space, that is, keeps it unitary on the constructed space.** Each prime step is one such extension. It is
equivalent to the positivity target of section 1, not weaker or stronger, because isometry is automatic and unitarity
on a Hilbert space is positivity.

**What the numbers say [numerical].**
- **Unitary at every step computed:** for the full arithmetic, every step up to a = 1.25 is a unitary extension with
  room (|k| <= 0.68).
- **Not unitary without the next prime:** the semilocal forms are exactly as scale invariant, since each place's term
  is translation invariant. Without the next prime, the extension stops being unitary within one to three cells of
  its entry, with |k| up to 77 (section 2, part 2).
- **What fails is positivity:** scale invariance holds in both cases; the full arithmetic keeps the extension unitary
  and the incomplete one does not.

---

## 2. Step 1: what carries P(k) to P(k+1)

**Exact statement [classical] + [proved here]:** P(k) -> P(k+1) holds iff, for every lag m from the first one beyond
2a_k up to 2a_{k+1} (on every grid), the new entry t_m lies in (t^_m - E_{m-1}, t^_m + E_{m-1}). The new prime p_{k+1}
enters t_m at the lags with |log p_{k+1} - m eps| < r eps. Those lags sit at the corner of the matrix, the boundary.

**What the numbers show [numerical]** (`induction.log`, parts 1 and 4; eps = 0.05 and 0.025; r = 1 and 3; support up to
a = 1.25):

| quantity | step cells (r = 1) | C^1 spline cells (r = 3) |
|---|---|---|
| all sections positive | yes | yes |
| max reflection coefficient |k| | 0.36 | 0.68 (eps 0.05), 0.50 (eps 0.025) |
| margin lambda_min / t_0 at a = 1.2 | 8.3e-4 | 1.2e-9 (eps 0.05), 1.2e-11 (eps 0.025) |
| prediction error E / t_0 at a = 1.2 | 0.24 | 7.5e-4 (eps 0.05), 1.5e-3 (eps 0.025) |
| largest single prime term, in units of E | 1.7 (p = 11) | 722 (p = 7, lag 39) |

- **Each step has room in the recursion's own coordinates.** No |k| comes close to 1. In those coordinates the
  induction does not look critical.
- **The room is bought by cancellation.** At the central lags of a prime (r = 3), the prime's own term is tens to
  hundreds of interval radii: -64 for 3, -90 for 4, -290 for 5, -722 for 7, -440 for 9, -429 for 11. The actual
  k stays below 0.7 in absolute value. So the value extrapolated from the smaller primes and the real place predicts the new prime's
  contribution to within less than one radius. Part of that prediction is the extrapolation of the same prime's spline
  tail from its first lags; at the first lag where a prime's term is not negligible, nothing of it is known yet, and
  there the term is about one radius (-0.84 for 3, -1.4 for 5).
- **The margin drops at each entry by a factor.** lambda_min just before and just after each prime power (eps 0.025,
  r = 3, part 4):

  | n | a before | lambda_min before | a after | lambda_min after | after / before | without p, after |
  |---|---|---|---|---|---|---|
  | 2 | 0.338 | 3.4e-3 | 0.413 | 2.1e-4 | 0.062 | -0.080 |
  | 3 | 0.537 | 2.8e-7 | 0.613 | 2.4e-9 | 0.0086 | -0.158 |
  | 4 | 0.688 | 9.3e-10 | 0.763 | 2.5e-10 | 0.27 | -0.552 |
  | 5 | 0.800 | 2.0e-10 | 0.875 | 9.1e-11 | 0.46 | -0.307 |
  | 7 | 0.963 | 5.1e-11 | 1.038 | 3.3e-11 | 0.65 | -0.362 |
  | 9 | 1.088 | 2.7e-11 | 1.163 | 1.8e-11 | 0.67 | -0.729 |

  The "without p" column drops the entering prime and all its powers. The margin then becomes negative and of order
  t_0, not slightly negative. The later after/before factors are larger partly because the grid stops resolving the
  smallest eigenvalue (lambda_min near 1e-11 is close to what 98 spline cells can represent); the decay per 0.1 in a
  is 2 to 2.5 decades while it is resolved.
- **Semilocal sections fail at once (part 2).** Keep the real place and the primes below p*. Positivity then fails
  within one to three lags of the first lag that holds log p*: at a = 0.388, 0.575, 0.825, 0.988, 1.213 against
  (1/2) log p* = 0.347, 0.549, 0.805, 0.973, 1.199 (eps 0.025, r = 3). The delay shrinks with p and with eps,
  sharper than the 0.03 to 0.04 of `SEMILOCAL.md` section 3. The failing k is far outside the disk (k = -77 for
  p* = 2 at eps 0.05, r = 3).

**So:** what carries P(k) to P(k+1) is the new prime itself, landing where the smaller scales predict, to within the
current radius. Leave it out and the step fails immediately. Weaken its weight by a little and the step fails too
(section 4). **[reading]**, from the numbers.

---

## 3. Step 2: the dichotomy transferred: boundary part and bulk

**The new prime is a pure boundary term at entry [proved here].**
- **Where it acts:** at support a = a_k + delta, the prime p_{k+1} contributes -Lambda(p) p^{-1/2} [h(log p) +
  h(-log p)], with h(log p) = int f(x) f(x - log p) dx. With log p = 2a_k the integrand lives on x in
  [a_k - delta, a_k + delta], with x - log p in [-a_k - delta, -a_k + delta]. So the term couples a band of width
  2 delta at the right end to a band of width 2 delta at the left end, and nothing else.
- **"The rest" is zero at entry:** nothing of p_{k+1} acts in the bulk until the support has grown well past
  (1/2) log p_{k+1}; the bulk changes only through the larger space and through later prime powers.
- **It is not small:** as an operator it is Lambda(p) p^{-1/2} times a partial isometry (translation by log p between
  the two bands), so its norm is log p / sqrt p for every delta > 0. It is localised, not attenuated. Whether it
  hurts depends on how much of the near-null directions lives on the end bands. That is the collar question:
  attenuation (mass at the ends) against amplification (the inverse margin, 1/lambda(a), in the Schur complement).

**The boundary part is exactly the prime side [proved here].** Take two bumps f_y = g(. - y) +- g(. + y) with g fixed,
supported in [-b, b]. Translation invariance gives

  W(f_y) = 2 W(g) +- 2 Y(2y),  Y(u) = E( (h_g(. - u) + h_g(. + u)) / 2 ),

and Y(m eps) is exactly the Toeplitz moment t_m when g is a cell. So:
- **Two-bump positivity is a bounded-moment condition.** It is equivalent to |Y(u)| <= W(g) = Y(0) for all u: the
  2 x 2 minors (`toep_moment_bound` **[Lean]**).
- **Y is the smoothed square-root prime fluctuation.** On the arithmetic side, Y(u) = c_g e^{u/2} - sum_n Lambda(n)
  n^{-1/2} h_g(log n - u) + O(e^{-u/2}). Up to the normalisation e^{-u/2}, that is the prime count psi(x) - x
  smoothed at x = e^u. So two-bump positivity is "smoothed |psi(x) - x| <= C sqrt(x)".
- **[proved here] A one-sided version with sub-exponential loss already excludes zeros (Landau).** Suppose
  Y(u) <= K e^{theta u} for u >= 0, which follows from W(f_y) >= -C e^{2 theta a} ||f_y||^2 for the minus sign. Then
  phi(u) = K e^{theta u} - Y(u) >= 0. Its Laplace transform is K/(s - theta) - sum_rho h^_g(t_rho) s/(s^2 + t_rho^2),
  meromorphic on C (the zeros are locally finite, and w^_g the transform of h_g, decays fast in horizontal strips).
  - **Landau:** a positive function's transform is analytic right of its abscissa, which is a real singularity. The
    only real singularity is s = theta, because xi has no real zeros. So the transform is analytic in Re s > theta.
  - **The conclusion:** an off-line zero rho = 1/2 + beta + i gamma gives a pole at s = beta + i gamma with residue
    h^_g(t_rho) times its multiplicity, non-zero for generic g. So no zero has beta > theta. Letting theta -> 0 gives
    RH.

  This is the same Pringsheim-Landau theorem as `ProofPhase/Bridge/Laplace.lean` (`laplace_landau`) and as the Lean RH
  proof's `landau_window` (`GUIDE.md`) **[classical]** for the theorem.

**What this says about the dichotomy [reading]:**
- **The split:** Weil's form at support a splits naturally into a **boundary part** (the coupling of the two ends,
  the moments t_m, two-bump positivity) and a **bulk part** (all sections positive).
- **The boundary part, all scales:** it is the prime-distribution statement psi(x) = x + O(sqrt x) in smoothed form.
  Through Landau, even a lossy one-sided version of it gives RH. It is what the other proof establishes, by Stepanov's
  balance and Arakelov heights (`GUIDE.md`, "the large part").
- **The bulk part, all scales:** it is Weil positivity, the positivity route.
- **At one scale:** bulk implies boundary (minors of a positive matrix). Boundary does not imply bulk; the moments
  are bounded long before a section fails.
- **At all scales:** each implies RH, and RH implies both.
- **What "controlled like a collar" means here:** the boundary term is controlled exactly when the square-root prime
  bound holds. It is attenuated, in the sense of the collar, only after the other proof's work is done. The positivity
  induction cannot borrow it without becoming the other proof.

---

## 4. Step 3: the integer quantum

**What an exact step needs [Lean].** `norm_le_of_exp_bound`: if finitely many distinct alpha_i with non-zero
weights c_i satisfy ||sum c_i alpha_i^n|| <= C rho^n for every n, then every |alpha_i| <= rho, and the constant C
disappears.
- **Why:** invert the Vandermonde matrix on any k consecutive powers, so each c_i alpha_i^N is bounded by K rho^N,
  and a ratio |alpha_i|/rho > 1 would grow without bound.
- **What it shows:** this is the "exact step from a lossy estimate". It needs only that the spectrum is finite, and
  weights that cannot cancel.
- **Over a finite field:** it is how Stepanov's point count O(q^{n/2}), valid for all n, gives |alpha| = sqrt q
  exactly **[classical]**.
- **Over the integers:** the spectrum is infinite, and Landau's theorem takes the role of the Vandermonde inversion
  (section 3). It needs one-sidedness, that is positivity of the coefficients Lambda(n) >= 0.

**Where integrality enters the proved route [classical] + [reading].** In Stepanov's method the integer is the
vanishing order m of the auxiliary function. "At least m at every point" against "at most the degree" gives an error
of about q/m + m, smallest at m = sqrt q. In the Lean RH proof the same role is played by the chain length of theta
lifts, with error x/m + m (`GUIDE.md`, move 2). So the owner's "at least something must exist" (an integer
multiplicity, at least 1 per point) is exactly the quantum that produces the exponent 1/2. It does so **on the
boundary side**, for the prime count.

**On the positivity side the quantum is necessary but not sufficient.** Three findings:
- **[numerical] (part 3) The weights must be exact.** Multiply Lambda(p^j) by (1 + eta) for one prime p. Positivity
  of all sections up to a = 1.25 then breaks at the following eta (halving search: eta breaks, eta/2 does not):

  | p | step cells, eta up | step cells, eta down | C^1 splines (eps 0.05), eta up | C^1 splines, eta down |
  |---|---|---|---|---|
  | 2 | 2.0e-3 | 3.1e-2 | 9.3e-10 | 1.5e-8 |
  | 3 | 3.9e-3 | 1.6e-2 | 1.9e-9 | 1.5e-8 |
  | 5 | 7.8e-3 | 1.6e-2 | 1.5e-8 | 3.0e-8 |
  | 7 | 1.6e-2 | 1.6e-2 | 2.4e-7 | 4.8e-7 |

  - **The tolerance tracks the margin:** about lambda_min of the resolving basis, 8e-4 for step cells and 1e-9 for
    splines.
  - **The tolerance is asymmetric:** a heavier prime breaks positivity sooner than a lighter one.
  - **It shrinks with the support:** since the margin collapses at least exponentially, the precision needed grows
    without bound. No continuous estimate (a weight known up to a fixed relative error) can carry the induction. The
    weights must be the exact integers' logarithms.
- **[classical] Integrality alone is not enough.** The exact weights Lambda(n) >= 0 are the Euler product's positivity.
  That weight positivity is insufficient (shown in `SEMILOCAL.md` 3a, `LEE-YANG.md` step 3 and `ORBITS.md` 3).
- **[classical] There is no integer count to step by.** Finite Euler products are zero-free, so no zero count is built
  up prime by prime. Zeros appear only in the infinite product (`LEE-YANG.md`). The integer that could be quantised
  (the number of zeros in a box) does not exist at any finite stage of this induction.

---

## 5. Step 4: the owner's coupling, de Branges and Krein

**The coupling, precisely [classical] (recalled) + [proved here] for the elementary parts.**
- **The Hermite-Biehler pair:** write E_h(z) = xi(1/2 + h - iz) for h > 0, with "real and imaginary halves"
  A_h = (E_h + E_h^*)/2 and B_h = i(E_h - E_h^*)/2, where E^*(z) = conj E(conj z).
  - Under RH, E_h is Hermite-Biehler for every h > 0, and then A_h, B_h have only real, interlacing zeros.
  - Conversely, if E_h is Hermite-Biehler, it has no zeros in the upper half-plane, so xi has no zeros with
    Re s > 1/2 + h. Letting h -> 0 gives RH.

  The direction from RH uses the Hadamard product; the converse is immediate. This frame for zeta is due to Lagarias
  (2005-2006, recalled, not re-read). It is the owner's "entangled real and imaginary halves forming a coupled
  existence", made exact.
- **Chains:** a positive form on PW_a (entire functions of exponential type a, square integrable on R) for every a
  gives nested Hilbert spaces of entire functions, PW_a inside PW_a' isometrically, because the form is the same
  form. That is a chain in de Branges's sense.
  - de Branges's theorems (recalled): the ordering theorem (isometrically contained spaces are totally ordered), and
    the correspondence of chains with canonical systems whose Hamiltonian is positive semidefinite.
  - The discrete form is the Szego recursion of section 1: reflection coefficients in the unit disk. The continuous
    form is Krein's systems, where positivity on [0, a] means the system's coefficient exists, without blow-up, up
    to a.
  - One axiom needs care: the frequency-weight part int |F|^2 Phi dr satisfies de Branges's division axiom
    (|(r - conj w)/(r - w)| = 1 on R) for any real weight. The pole term POLE (point evaluations at +-i/2) does not,
    so it has to be split off first **[proved here]**, elementary.
- **Extension:** every positive section has positive extensions. They form the interval of section 1, Krein's
  extension theorem in discrete form **[classical]**. The induction asks whether the **arithmetic** extension, the next
  moment with the next prime's impulse, is among them.

**Does adding a prime correspond to a chain step? No, not one step.** **[numerical]** + **[reading]**:
- **Steps are scale steps:** the chain is indexed by the support a. Every increment of a is a step and needs the
  condition, prime or not.
- **What a prime does:** it is an impulse in the moments at lags near log p / eps, spread over 2r lags.
- **Prime steps look ordinary:** the reflection coefficients at lags carrying a prime power (mean |k| = 0.25, max
  0.50) look like those without (mean 0.20, max 0.43) (part 4).
- **The restatement:** "the chain stays Hermite-Biehler" is a correct restatement of the whole induction. The primes
  are where its coefficients are forced by arithmetic, and everything between them is forced by the real place
  alone.

**What is known, and where this differs.**
- **de Branges's programme (recalled):** de Branges proposed a specific positivity: a function built from zeta acting
  as a contraction, or positive operator, on a fixed de Branges space built from the Gamma factor. Conrey and Li
  (2000) showed that this condition fails for zeta and for Dirichlet L-functions **[classical]** (recalled).
- **What differs here:** the chain is not a fixed archimedean space with zeta as a multiplier. At each scale its form
  is the full arithmetic kernel, with every prime up to e^{2a}. So the Conrey-Li counterexample does not apply to it.
  Its step condition is true (RH is proved).
- **Where it would have to differ to be a proof:** it would need a rule that predicts each new reflection
  coefficient, or bounds it inside the disk, from the arithmetic up to that scale. The recursion gives k_N only after
  the moment t_N is known, and |k_N| < 1 is, scale by scale, the same statement as positivity at that scale. De
  Branges's theorems organise the chain but do not supply the rule **[reading]**.

---

## 6. Step 5: the numerics in one place

`py induction.py > induction.log` takes 58 s on the CPU, at 60-digit precision (mpmath).
- **Part 0 checks the functional:** E(h) against 60 zeros, to 1e-61.
- **Part 1:** the full form, the reflection coefficients and the prime-entry tables, for step cells and C^1 splines
  at eps = 0.05, and for splines at eps = 0.025.
- **Part 2:** semilocal sections, where positivity fails within 1 to 3 lags of the missing prime's entry.
- **Part 3:** the exactness of the weights.
- **Part 4:** the margin before and after each entry, and the coefficients by lag.

The structure of the increment, in one sentence **[numerical]**: at each prime entry the margin drops by a factor
(0.06 for 2, 0.009 for 3, then 0.3 to 0.7 per prime power while the grid resolves it). The step's room in the
recursion's coordinates stays O(1). The new prime's raw term is O(1) to O(700) radii and is cancelled by the
extrapolation from below. The prime's weight must be exact to about the margin.

Limit of the method: lambda_min near 1e-11 at a = 1.25 is about what 98 spline cells resolve. Going further needs more
cells and higher precision, and adds nothing to the structure.

---

## 7. Where it stops, and the relation to the four earlier forms

**Steps 1 to 5:**

| step | content | status |
|---|---|---|
| 1 | frame P(k); one step = one scalar condition (corner entry in the extrapolated interval) | **[classical]** + **[proved here]** |
| 2 | the margin is monotone and collapses; the step must be multiplicative | **[proved here]** (sketch for the collapse) |
| 3 | at entry, the new prime is a pure boundary term of norm log p / sqrt p | **[proved here]** |
| 4 | boundary part = two-bump positivity = smoothed square-root prime bound; with Landau, sub-exponential one-sided loss gives RH | **[proved here]**, on paper |
| 5 | finite spectrum: lossy bound is exact; one-grid criterion with finitely many atoms | **[Lean]** |
| 6 | the steps hold numerically up to a = 1.25 with room in the recursion, by cancellation; weights must be exact | **[numerical]** |
| 7 | **step lemma**: from the arithmetic up to p_{k+1} alone, put each new corner entry inside the extrapolated interval, i.e. lambda(a_{k+1}) >= c_k lambda(a_k) with c_k > 0 | **[open]**: the stop |

**Why step 7 cannot be closed with what is on the table [reading]:**
- **The interval is history-dependent:** its centre is a linear extrapolation from all smaller scales, and its radius
  is the product of all earlier (1 - k^2).
- **No local rule is known:** a rule that sees only the new prime and a bounded window of scales would have to
  predict a quantity that depends on every smaller prime. No such rule is known.
- **The direct bound is circular:** bounding the margin's logarithmic rate of decrease amounts to locating the lowest
  zeros (the collapse rate is set by the zero-free gap), so the bound uses the zeros.

**The same obstacle in the four earlier forms.** Step 7 is the "weakest structure" obstacle of `ATTEMPT.md` step 4,
sliced by scale, and each of the four forms would supply it:
1. **Weil Hilbert space (ATTEMPT step 4):** the union of the chain is that Hilbert space. Its existence means
   positivity at every scale, which is the conclusion of the induction, and the induction builds it slice by slice.
   Same obstacle, cut by support; no gain, no loss.
2. **Critical ferromagnet (LEE-YANG 5c):** Lee-Yang theory has an induction that works. Asano contraction adds one
   site at a time and preserves the circle property exactly, because it is local and algebraic. Here the step is not
   local; it is the history-dependent interval. A ferromagnet whose block spin has law Phi would make the step local
   (Asano). It is a stronger structure that would imply step 7.
3. **Deninger space (ORBITS step 6):** the support a is the flow time. Positivity up to support a is the Hodge form on
   the part of cohomology seen by orbits of length at most 2a, and each new prime is a new closed orbit entering at
   time log p. A geometric positive Hodge form would give every step at once. It is stronger and would imply step 7.
4. **Hermite-Biehler chain (this note, section 5):** step 7 is literally "the next reflection coefficient lies in the
   disk". It is the same obstacle in coordinates where each step looks easy (|k| <= 0.68), because the difficulty has
   moved into the map from arithmetic moments to coefficients, which amplifies by 1/E.

So all four are one obstacle. ATTEMPT step 4 is the weakest form and step 7 is its scale-by-scale slicing.
Ferromagnet and Deninger space would each give it. The Hermite-Biehler chain is it, in the coordinates where it looks
smallest.

---

## 8. DMP reading (separate; not mathematics)

> **The owner's framing (PREP.md, "GRH from the other side"): "The other proof seeks to prove that the primes are
> distributed evenly along the real numbers, while what we seek to prove is this: The entangled real and imaginary
> halves, when running in a DMP-complete system, form a coupled existence, spanned in locality by the real and in
> possibility by the imaginary. This system is proven sound through construction, which shows it can run as content
> in DMP, thus having a positive existence." This section says what the round shows about it. Nothing here is a
> mathematical result.**

- **"From the other side": supported, and now exact.** Weil's form at each scale has two parts:
  - The boundary part (the coupling of the two ends) is exactly "the primes are distributed evenly", the smoothed
    square-root prime count, which the other proof establishes and Landau turns into RH (section 3).
  - The bulk part (all sections positive) is the positivity route.

  At each scale, the bulk implies the boundary; over all scales both are RH. So the two proofs are the two halves of
  one form. The other proof does the boundary, and we ask for the bulk. *Exact* for the split; *analogy* for "sides".
- **"Entangled real and imaginary halves, a coupled existence": supported as a structure.** The Hermite-Biehler pair
  A_h, B_h of xi(1/2 + h - iz) is a real and an imaginary half whose coupling (the Hermite-Biehler inequality) forces
  both onto real, interlacing zeros, and that coupling is equivalent to RH (section 5).
  - "Spanned in locality by the real": the support a, where each prime acts at its place log p, is the real
    direction.
  - "In possibility by the imaginary": the frequency, where the zeros sit, is the imaginary direction.

  The Toeplitz sections are literally the zeros (possibility) seen through finite windows of the primes (locality).
  *Analogy* for the words, *exact* for the structure.
- **"Proven sound through construction": this is what the induction tries, and the numbers show its texture.**
  - Building positivity up scale by scale works at every step computed, and each new prime "fits what was built
    before" to within the current margin: it lands inside the window predicted by everything smaller.
  - Leave it out and the construction fails at once. Change its weight by a part in a billion and it fails too.
  - That is a vivid picture of construction under exact constraints. But the construction is checked, not derived:
    no rule from the arithmetic predicts the window, and that rule is step 7.
- **"At least something has to exist" (the integer quantum): supported, on the other side.** The integer multiplicity
  (at least m at every point) is precisely what produces the exponent 1/2 in Stepanov's method and in the Lean proof's
  theta-lift chain. On our side, exact integer weights are necessary to exponential precision but do not by
  themselves give positivity (section 4).
- **"This existence space is essentially scale invariant, which gives a flat curvature, which universally certifies
  existence and binds to G0" (the owner, same round).** Read with the coordinator's mapping (section 1a: the flat
  scaling characters are exactly the critical line).
  - **Supported:** the target is exactly "scaling stays flat" (unitary). The critical line is the set of flat
    characters, and each step of the induction is one unitary extension of the scaling action. The numbers show the
    full arithmetic keeping it unitary at every step computed, with room. *Exact* for the mapping; **[numerical]** for
    the steps.
  - **Contradicted as stated: scale invariance does not by itself certify.** The scaling action preserves Weil's form
    at every scale automatically, so invariance gives the isometry, a flatness in the indefinite sense. The semilocal
    forms are exactly as scale invariant, and they go negative within one to three cells of a missing prime (|k| up
    to 77). In the finite model, an indefinite form preserved exactly allows the off-line pair 3/4, 1/4
    (`ORBITS.md`). Flatness in the sense that certifies (unitary on a positive space) needs the complete set of primes
    below the scale together with the real place. Invariance supplies none of that.
  - **"Binds to G0":** there is no mathematical counterpart here to test, so no verdict.
- **"A contradiction is a disagreement at G0, excised at once; only the remnant of its not existing remains" (the
  owner, PREP.md; the coordinator reads it as reductio ad absurdum as a process, whose remnant is the refutation
  not-A).**
  - **Where it applies exactly.** Every route to the line in this work ends in such an excision.
    - Landau (section 3): assume an off-line zero; it puts a pole where a positive transform must be analytic;
      contradiction. The remnant is the zero-free half-plane Re s > 1/2 + theta.
    - The grid model: an off-line zero is an atom off the circle, whose moments grow, while positive sections bound
      them. `norm_le_of_exp_bound` and `atoms_inside_circle` **[Lean]** are proofs by contradiction of this shape.
    - The Lean RH proof: it splits on `lt_trichotomy s.re (1/2)` and empties the side right of 1/2 the same way
      (`GUIDE.md`).

    *Exact* for the logical form.
  - **Where it does not apply.** A duality alone produces no contradiction. `krein_off_line` (`ORBITS.md`) is a
    consistent model in which a form is preserved exactly and the off-line pair 3/4, 1/4 exists. There is nothing to
    excise until positivity (or the one-sided prime bound) is present, because the contradiction is between the
    off-line zero and that premise.
  - **In the induction.** An established contradiction at a step would be a reflection coefficient with |k| >= 1: a
    negative direction of the form, as in the semilocal sections. With the full arithmetic, none arose up to
    a = 1.25 **[numerical]**.
  - **Does it add anything to the open step? No.** The reading describes how a proof concludes once the premise is
    in hand. Step 7 is to obtain the premise (positivity scale by scale, from arithmetic alone), so that a
    contradiction can never be established. The reading supplies the form of the last line, not the step.
- **Verdict:**
  - **supports** the reading of the two proofs as two sides of one structure (boundary against bulk, prime side against
    zero side);
  - **supports** the coupled-halves picture as the Hermite-Biehler frame;
  - **supports** "flat curvature" as the target (unitary scaling, section 1a), but **contradicts** "scale invariance
    universally certifies": invariance gives the isometry for free, while unitarity needs positivity, which the
    invariant semilocal forms lack;
  - **neutral** on "proven sound through construction": the construction holds wherever computed but is not proved,
    and its open step is the same obstacle as before, sliced by scale.

---

## 9. Files and references

**Files (this round):**
- `docs/rh-guide/grh/INDUCTION.md` (this note).
- `docs/rh-guide/grh/induction.py` and `induction.log` (numerics, CPU, 58 s).
- `docs/mass-gap/formal/ProofPhase/GRH/Induction.lean`, with five theorems: `norm_le_of_exp_bound`,
  `toep_moment_bound`, `atomic_toep_nonneg`, `atoms_inside_circle`, `atoms_on_circle`.
- `docs/rh-guide/grh/axioms-induction.sh` and `.log` (standard three axioms for all five; no sorry, admit,
  native_decide or axiom).

**References (recalled, not re-read in this session):**
- Weil's explicit formula and positivity criterion (1952).
- Yoshida, Hermitian forms attached to zeta functions (1992).
- Connes and Consani, Weil positivity and trace formula, the archimedean place (2021).
- Szego's recursion and theorem; Levinson-Durbin; the Schur algorithm; Krein's extension theorem (1940) and Krein
  systems.
- de Branges, Hilbert Spaces of Entire Functions (1968).
- Conrey and Li, On the positivity condition of de Branges (2000).
- Lagarias, Hilbert spaces of entire functions and Dirichlet L-functions, and zero spacing for differenced
  L-functions (2005-2006).
- Slepian and Pollak, prolate spheroidal functions (1961).
- Landau's theorem (1905).
- Stepanov's method (1969), with Bombieri's version (1974).
