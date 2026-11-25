# A variational form of Weil positivity: the ground state of the running section

Private working note, 2026-11-23. It follows `INDUCTION.md` (the scale-by-scale induction and its step lemma) and
the four forms before it: `ATTEMPT.md` step 4, `LEE-YANG.md`, `ORBITS.md`, and the Hermite-Biehler chain in
`INDUCTION.md` section 5. The question comes from the owner's reading in PREP.md ("Three answers ...", item (b)):
"the self asserting effects of the remnants of acts, which is the mechanism which forces the optimization once a
running state has been established". The task: is there a variational principle whose second variation is Weil's form,
or whose stability is equivalent to positivity? If so, what would minimality give, and what would have to be proved?

As in `INDUCTION.md`, RH is proved (Lean) elsewhere in this repository, so every positivity below is true. The open
question is whether a variational principle proves it **independently**, from arithmetic alone.

**Claim marks** are as in `INDUCTION.md`:
- **[numerical]** = `variational.py` (output `variational.log`, 26 s), on the grid of `induction.py`;
- **[classical]** = known; "recalled" means recalled, not re-read in this session; "abstract" means only the abstract
  was read;
- **[proved here]** = argued in this note, on paper unless it says Lean;
- **[Lean]** = `ProofPhase/GRH/Variational.lean`, 4 theorems, standard axioms only (`axioms-variational.log`);
- **[reading]** = interpretation;
- **[open]** = not settled.

---

## 0. The answers

1. **Yes, and it is already in the frame: the ground state of the running section.** On every section (Weil's form
   restricted to test functions of support a), minimise the form over unit vectors. The minimum is the margin
   lambda_min(a) of `INDUCTION.md`. The minimiser, the ground state, carries real information. Its polynomial has all
   its zeros exactly on the unit circle, which is the critical line in grid coordinates (to 1e-53). As primes enter,
   these zeros lock onto the zeros of zeta. With the primes up to 11 (support 1.225, r = 3), the first ordinate
   14.134725 is reproduced to 3e-7, and 21.022 and 25.011 to 4e-4. Without the primes (archimedean place only) the
   ground-state zeros are evenly spaced and carry no zeta information. **[numerical]**
2. **The reality of the minimiser's zeros is free; the sign of the minimum is not.** By Caratheodory-Fejer and
   Pisarenko, the minimum splits the section into two parts: N - 1 positive atoms on the circle, at the ground state's
   zeros, plus a uniform remnant of size lambda_min. The atoms are on the circle for every real symmetric Toeplitz
   section, positive or not. Positivity is exactly the statement that the remnant is nonnegative. **[classical]**
3. **"Positivity = stability of the minimum" holds, but only as a tautology.** Weil's form is quadratic, so it is
   its own second variation. "The trivial state minimises" is positivity, word for word (Lean template). The
   arithmetic configuration is data here, not the thing being varied.
4. **Varying the configuration instead (the primes as the thing being optimised) does not give an optimum.** The
   margin is a concave function of the prime weights: a minimum of linear functions. The positive configurations form
   a convex set (Lean). At every scale computed, the arithmetic configuration is not a stationary point of the margin.
   At support 1.225 (r = 3), scaling the prime 2 by (1 + s) changes the margin at rate -1.01, while the margin itself
   is 1e-9. So the true primes sit about 1e-9 from the edge of the positive window, not at its centre. **[numerical]**
5. **The stop, the sixth face of the same obstacle.** The open step is the **sign of the remnant**: from arithmetic
   alone, show that lambda_min(a) >= 0 at every support. Equivalently, on one grid, show that the ground states
   converge to the zero measure (a positive measure carrying the true moments). By Hurwitz, convergence of the ground states to xi would give
   RH without the sign. But on a grid that convergence is equivalent to the sign (section 2), and the continuum
   result of Andrews-Connes-La Gatta (2026, abstract) assumes the positivity. This is the step lemma of
   `INDUCTION.md`, read at one scale instead of between scales (section 5).

---

## 1. The candidates

### 1a. The Rayleigh (Dirichlet) principle on a section, and its dual

Take the Toeplitz section T_N of Weil's form on N grid cells (support a = (N - 1 + r) eps / 2), as in `INDUCTION.md`
section 1. Its least eigenvalue is lambda_min = min over |c| = 1 of c* T_N c. The minimiser v is the ground state.

- **Second variation:** the Rayleigh functional's Hessian at the trivial state c = 0 is T_N itself. "0 is a stable
  minimum" means T_N >= 0. In the finite template (`min_at_zero_iff`, Lean), 0 minimises b.x + x.Ax exactly when
  b = 0 (first variation) and A >= 0 (second variation). Nothing is gained by calling it stability.
- **The dual, and why the minimiser is worth having [classical, recalled: Caratheodory-Fejer; Pisarenko 1973]:**
  - The dual problem is lambda_min = max { kappa : T_N - kappa I >= 0 }.
  - When lambda_min is simple, T_N - lambda_min I is a singular positive Toeplitz matrix of rank N - 1. It is
    therefore the moment matrix of a unique positive measure with N - 1 atoms on the unit circle.
  - The atoms sit at the zeros of the ground-state polynomial sum_j v_j z^j.
  - So each section splits as **(uniform measure of mass lambda_min) + (N - 1 atoms on the circle)**.
  - The atoms lie on the circle (on the line) whatever the sign of lambda_min. Positivity is the sign of the uniform
    remnant.
  - A related classical fact (recalled: Makhoul 1981; Delsarte, Genin and Kamp): the extreme eigenvectors of a real
    symmetric Toeplitz matrix are symmetric or antisymmetric, and their polynomials have unimodular zeros.
- **The same principle in the continuum [abstract]:** Andrews, Connes and La Gatta, arXiv:2611.13129 (November
  2026), "The uncertainty operator, the Weil ground state and the zeros of zeta":
  - They apply the Dirichlet principle to Weil's form on L^2([lambda^-1, lambda]) with the primes up to lambda^2.
  - The Mellin transform of the ground state has zeros that they prove real whenever the lowest eigenvalue is simple
    and even.
  - Numerically, those zeros reproduce the zeros of zeta (the first 1000 from lambda^2 = 250).
  - Positivity, and convergence of the ground state to xi, are stated there under hypotheses: QW >= 0 together with
    a "ladder" hypothesis.
  - The grid version here is the same phenomenon in Toeplitz coordinates. Its zeros-on-the-circle statement is the
    Pisarenko fact above.

**Numbers [numerical]** (grid r = 3, eps = 0.05; ground state simple and even in every full section; |z| = 1 to
1e-53):

| support a | primes present | lambda_min / t0 | ground-state angle/eps nearest the first zeros, and the error |
|---|---|---|---|
| 0.575 | 2, 3 | 1.3e-7 | 14.135 (7e-6), 21.022 (8e-4), 25.011 (1.4e-2), 30.425 (0.28) |
| 0.875 | 2, 3, 5 | 7.3e-9 | 14.135 (2e-4), 21.022 (4e-4), 25.011 (1.2e-3), 30.425 (3e-4), 32.935 (3e-3), 37.586 (6e-3) |
| 1.225 | 2, 3, 5, 7, 11 | 9.9e-10 | 14.135 (2.8e-7), 21.022 (8e-5), 25.011 (4e-4), 30.425 (1e-3), 32.935 (7e-3), 37.586 (3e-3), 43.327 (2e-2) |
| 1.225, control: archimedean place only | none | -3.2 (not positive) | evenly spaced angles, step about 2.65; nothing tracks zeta (errors 0.3 to 3) |

- **The ground state also has zeros that track no zeta zero** (for example 5.7, 8.6, 11.2, 16.8, 19.4 and 26.4 at
  support 1.225). A section has N - 1 atoms; the true measure has about 80 dominant atoms below the alias limit
  2 pi / eps. The extra atoms fill the gaps.
- **The r = 1 grid (tent cells) tracks the zeros only roughly (errors of 0.004 to 1).** Its weights |b^(t)|^2 decay
  like t^-2, so high zeros blur the low ones.
- **The pattern is that of a finite-moment reconstruction.** The moments t_m are, by the explicit formula, both prime
  sums and zero sums. The minimisation recovers the dominant atoms (the low zeros) from the prime side, and the
  primes are what move the evenly spaced archimedean pattern onto the zeta ordinates.

### 1b. Szego's extremal problem: the induction is already variational

- **The Szego minimum is the margin of the induction [classical]:** the prediction error E_N of `INDUCTION.md`
  (Levinson) is Szego's minimum, the minimum of p* T_{N+1} p over monic polynomials p of degree N. Its minimiser is
  the orthogonal polynomial. Then T_{N+1} > 0 exactly when E_N > 0. Since a monic p has |p| >= 1,
  lambda_min(T_{N+1}) <= E_N.
- **The margin collapse is the Kolmogorov-Szego formula [classical, recalled]:**
  - On one grid the zero measure is purely atomic on the circle, with weights |b^(t_rho)|^2.
  - By Kolmogorov-Szego, E_N decreases to exp( integral of log w_ac ), where w_ac is the density of the absolutely
    continuous part. Here w_ac = 0, so E_N -> 0.
  - In prediction language the process is deterministic: the one-step remnant vanishes as the history grows.
  - This is the collapse found numerically in `INDUCTION.md` (lambda_min about 1e-11 by a = 1.24), now with its
    reason. It also shows why no bound of the form "margin >= constant" can exist on a fixed grid.

### 1c. Varying the configuration: concave margin, convex positive set, no optimum at finite scale

The moments are linear in the prime weights Lambda(n) (explicit formula). So each Toeplitz form is linear in the
configuration.
- **Convexity [Lean, `toep_pos_convex`]:** the configurations with all sections positive form a convex set.
- **Concavity [proved here]:** the margin, a minimum of linear functions, is concave.
- So "optimising" the configuration means maximising the margin.

**Is the arithmetic configuration the maximiser? [numerical]** The test is to scale Lambda(p^j) by (1 + s), for all
powers of one prime, and read off the first variation d(lambda_min/t0)/ds at s = 0 (Hellmann-Feynman, with v the
ground state):

| grid, support | lambda_min/t0 | slope for p = 2 | p = 3 | p = 5 | p = 7 |
|---|---|---|---|---|---|
| r = 3, a = 1.225 | 9.9e-10 | -1.01 | -0.42 | -0.038 | -0.0017 |
| r = 3, a = 0.875 | 7.3e-9 | -0.43 | -0.041 | -4e-6 | 0 (not yet entered) |
| r = 1, a = 1.225 | 8.3e-4 | -0.51 | -0.32 | -0.11 | -0.027 |

- **The slope is far from zero, so the true configuration is not a stationary point.**
- **The zero crossing on the + side** falls at s of about lambda_min / |slope|, which is 1e-9 for p = 2. This matches
  `induction.log` part 3 independently: there +9.3e-10 breaks a section and +4.7e-10 does not. That window was found
  by halving over all sections up to 1.25.
- **The positive window is lopsided:** its edges lie between -1.5e-8 and -7.5e-9 below and between +4.7e-10 and +9.3e-10 above (p = 2, r = 3). Since the margin is concave, its
  maximum lies at s < 0.
- **So, at every finite scale, the primes sit near the edge of the positive set, not at its optimum.**

**In the limit, rigidity rather than optimality [proved here, sketch].** Scaling all powers of p by (1 + s) with s
not 0 multiplies the Euler product by (1 - p^-w)^(-s) (w the complex variable) up to the functional-equation partner. That adds atoms of weight
of order s at Re s = 0 and Re s = 1, on the lines through the zeros of 1 - p^-s, a distance 1/2 from the critical line.
A positive form cannot carry an off-line atom (Weil's criterion; on a grid, `atoms_on_circle` in finite form). So
along each such line the windows shrink to the single point s = 0. The arithmetic configuration is the unique
positive point on these lines, an extreme point of the limit set. That is rigidity, and it already assumes the
positivity of zeta itself.

### 1d. The log-gas (random matrices): equilibrium, but of the wrong kind

- **The zeros match a Gibbs ensemble, not an energy minimiser [classical, recalled]:** their local statistics match
  GUE (Montgomery's pair correlation; Rudnick-Sarnak; Odlyzko's numerics). GUE eigenvalues are a log-gas at
  temperature beta = 2. That is a Gibbs ensemble, not an energy minimiser: the zero-temperature minimiser is a
  lattice, and the zeros are not equally spaced.
- **Reality is put in, not derived:** the matrices are Hermitian.
- **A principle at the level of densities cannot see an exceptional zero [proved here]:**
  - Changing finitely many atoms, or a density-zero set, leaves the limiting empirical measure unchanged, and with
    it any functional of that limit.
  - At that level the concentration on the line is already a theorem: almost all zeros lie within any fixed distance
    of the line (Bohr-Landau; Selberg's positive proportion on the line; recalled).
  - What RH adds is exactly the density-zero exceptional set that such a principle cannot see.
- **The log-energy's Hessian is positive whatever the configuration:** -log|x - y| is conditionally positive
  definite. So its stability is unrelated to Weil's form.

### 1e. The explicit formula as a fixed point between primes and zeros

- **As an identity it has no stability [proved here]:** primes determine zeros and zeros determine primes. Taken as a
  fixed point, it is an identity with nothing to vary, so it has no notion of stability.
- **Section 1a realises the prime-to-zero direction as a minimisation:** the primes up to e^(2a) give the section,
  and the ground state gives approximate zeros on the line. That is the closest thing to a variational fixed point
  that is actually available.
- **Integer regularity alone cannot force the zeros [classical, abstract]:** Diamond, Montgomery and Vorhauer,
  "Beurling primes with large oscillation", Math. Ann. 334 (2006), build a Beurling system of generalised primes
  whose integers are very regularly distributed, while its primes oscillate far more than RH allows. So its zeta has
  zeros off the line.
  - The integer quantum must enter through the specific arithmetic, not through counting regularity
    (`INDUCTION.md` section 4).
  - A variational principle posed on configurations with regular integers would have such systems as competitors.

### 1f. Connes-Consani and the prolate operator

- **Connes-Consani [abstract]:** Connes and Consani, arXiv:2006.13771, "Weil positivity and trace formula, the
  archimedean place". The abstract offers a potential conceptual reason for Weil positivity at the archimedean place.
  It works in the semilocal trace-formula frame and writes the gap between the Weil distribution and the Sonin trace
  in prolate spheroidal functions, controlled by Toeplitz-matrix theory.
- **Prolate functions are themselves extremisers:** they solve Slepian's concentration problem (maximal energy in a
  time window among band-limited functions).
- **Andrews-Connes-La Gatta (section 1a) is the semilocal continuation:** it ties Weil's form to the uncertainty
  operator 2 - P - P^, which the prolate functions diagonalise.
- **Our control row [numerical]:** the archimedean place alone is not positive at support 1.225 (lambda_min / t0 =
  -3.2; odd ground state). `induction.log` part 2 shows it positive up to about 0.39 to 0.43, just past
  (1/2) log 2 = 0.347, where the prime 2 enters. That is consistent with an archimedean positivity window ending
  near (1/2) log 2.

---

## 2. What minimality gives, and what would have to be proved

**What comes free:**
- the minimiser exists at every scale;
- its zeros lie on the line (Pisarenko);
- it is simple and even in every full section computed;
- its zeros converge numerically onto the zeta zeros as primes enter (section 1a).

**Route A: the sign of the minimum.** lambda_min(a) >= 0 for every a is Weil positivity, so RH. Minimality adds
nothing to the sign. **[open]**: this is the step.

**Route B: convergence of the minimiser (Hurwitz) [classical + proved here]:**
- **The Hurwitz route:** if the ground-state functions, suitably normalised, converge locally uniformly to xi, then
  by Hurwitz's theorem every zero of xi is a limit of real zeros, hence real. That is RH, with no need for the sign of
  lambda_min. It is the most attractive form of the principle.
- **On one grid, convergence and sign coincide:**
  - The Pisarenko measures of the sections are lambda_min,N U + alpha_N, where U is the uniform measure on the circle
    and alpha_N >= 0 has mass t_0 - lambda_min,N.
  - Their moments equal t_m for |m| < N.
  - So alpha_N has moments t_m - lambda_min,N delta_{m,0}.
  - If the alpha_N converge weakly to a positive measure carrying the true moments t_m, then lambda_min,N -> 0 and
    every section is positive, since its form is that measure's.
  - Conversely, if every section is positive, then lambda_min,N decreases to a limit L >= 0. Since
    lambda_min <= E_N -> 0 (section 1b), L = 0. The alpha_N have bounded mass, and their moments tend to t_m. Moments
    determine a measure on the circle, so the alpha_N converge to the zero measure.
  - So "the ground-state atoms converge to the zero measure" is equivalent to positivity on that grid. Route B is
    Route A in other words.
- **In the continuum:** the abstract of Andrews-Connes-La Gatta bounds the distance of the ground state to the target
  (Mellin transform xi/4) under QW >= 0 plus a ladder hypothesis. So their convergence also uses the positivity.
  **[open]**: unconditional convergence.

**Route C: the configuration as optimiser.** This fails at finite scale (section 1c): the primes are not
stationary for the margin. In the limit it reduces to rigidity, which presupposes positivity.

---

## 3. Lean

`ProofPhase/GRH/Variational.lean` (imports `Induction.lean`). The build is clean, with no warnings in the file, and
`axioms-variational.log` shows propext, Classical.choice and Quot.sound only:
- `line_min_iff`: a t + q t^2 >= 0 for all real t iff a = 0 and q >= 0.
- `min_at_zero_iff`: 0 minimises b.x + x.(A x) on R^n iff b = 0 and A is a nonnegative form (first and second
  variation). This is the finite template of "positivity = stability of the minimum".
- `toepForm_combo`, `toep_pos_convex`: the Toeplitz form is linear in the moments, and the positive moment sequences
  form a convex set. So the positive prime configurations are convex and the margin is concave in them.

The Pisarenko split (atoms of T - lambda_min I on the circle) would be the natural next Lean item. It needs the
singular case of Caratheodory-Fejer, which is not a small proof, and nothing downstream depends on it, so it was left
out.

---

## 4. Where it stops, and the relation to the five earlier forms

**The stop:**
- **The open step:** from the arithmetic up to e^(2a) alone, show that the uniform remnant lambda_min(a) of the
  section is nonnegative, at every support a. Equivalently, on one grid, show that the ground-state atoms converge to
  the zero measure. **[open]**
- **What does not help:**
  - Minimality supplies the minimiser and the reality of its zeros, but not the sign.
  - The margin collapses to zero (Kolmogorov-Szego), so the sign can never be won with room to spare at a fixed
    grid.

**The same obstacle in the five earlier forms:**
1. **Weil Hilbert space (ATTEMPT step 4):** its existence is "the remnant is nonnegative at every scale". Same
   statement.
2. **Critical ferromagnet (LEE-YANG):** there the circle property is the content (Lee-Yang, Asano). Here the circle
   property of the ground state is free (Pisarenko) and the content has moved into the sign of the remnant. The
   variational form shows sharply that "zeros on the line" for an approximant is cheap. The hard part is that the
   approximants are the right ones, i.e. that the remnant they leave is nonnegative.
3. **Deninger space (ORBITS step 6):** a positive Hodge form would make every remnant nonnegative at once. It is a
   stronger structure that would imply the step.
4. **Hermite-Biehler chain (INDUCTION section 5):** Szego's minimum E_N is the HB/Krein margin, and lambda_min <= E_N.
   These are two minimisations of the same form: the orthogonal polynomial (zeros inside the disk when positive) and
   the ground state (zeros on the circle always). They are one obstacle.
5. **Step lemma (INDUCTION section 7):** lambda(a_{k+1}) >= c_k lambda(a_k) is the remnant's survival from one scale
   to the next. The sign of the remnant is the same at one scale. With the collapse forced by Kolmogorov-Szego, the
   step lemma is the only form in which the sign could be propagated.

So all six are one obstacle. The variational form adds two precise facts:
- the line is reached for free by the minimiser (Pisarenko; Andrews-Connes-La Gatta);
- the true configuration is not an optimum at any finite scale, but it is rigid in the limit.

---

## 5. DMP reading (separate; not mathematics)

This section reads the owner's words against the mathematics above. Nothing here is a claim of the note.

- **"Remnants of acts":** the Pisarenko split gives the word a precise counterpart. At each running scale the section
  splits into what is asserted and what is left over. The asserted part is the N - 1 atoms, always on the critical
  line. The leftover is the uniform remnant lambda_min. The atoms being on the line is automatic. Whether the remnant
  is nonnegative is the whole question.
- **"Self asserting":** read as "the remnant keeps its sign as the state runs on", this is exactly the open step. The
  numbers support it: the remnant stays positive at every scale computed. But it shrinks to zero (1e-9 at support
  1.2, Kolmogorov-Szego), so it is asserted with less and less to spare.
- **"Forces the optimization once a running state has been established":**
  - The minimiser of every running section exists. As primes enter, its zeros are pulled from the evenly spaced
    archimedean pattern onto the zeta zeros (3e-7 for the first one with the primes up to 11). That is a measurable
    form of "forcing" by the running state.
  - What is optimised is the test function, given the arithmetic, not the arithmetic itself. The primes are not the
    optimum of the margin at any finite scale; they sit about 1e-9 from the edge of the positive set.
  - If the reading is pressed, the running state is held at the edge of stability rather than at an optimum, and it
    becomes the unique stable point only in the limit (rigidity).
- **Verdict:** the reading has an exact counterpart, the ground state of the running section with its zeros pinned to
  the line, and the numbers support it. It does not close the open step. The self-assertion of the remnant (its sign
  at every scale) is what would have to be proved, and it is the same obstacle as in the five earlier forms.

---

## 6. Files and references

**Files:**
- `variational.py`, `variational.log`: ground state, its zeros against the zeta ordinates, first variation in the
  prime weights, and the archimedean control (26 s, mpmath 60 digits). It reuses `induction.py`'s grid.
- `docs/mass-gap/formal/ProofPhase/GRH/Variational.lean`, `axioms-variational.sh`, `axioms-variational.log`.

**References:**
- R. Andrews, A. Connes, A. La Gatta, "The uncertainty operator, the Weil ground state and the zeros of zeta",
  arXiv:2611.13129 (2026). Abstract read.
- A. Connes, C. Consani, "Weil positivity and trace formula, the archimedean place", arXiv:2006.13771 (2020).
  Abstract read.
- H. Diamond, H. Montgomery, U. Vorhauer, "Beurling primes with large oscillation", Math. Ann. 334 (2006) 1-36.
  Abstract-level.
- Recalled:
  - Caratheodory-Fejer; V. F. Pisarenko (1973), harmonic retrieval;
  - J. Makhoul (1981), and Delsarte, Genin and Kamp, on eigenvectors of symmetric Toeplitz matrices;
  - Grenander-Szego, Toeplitz forms; Kolmogorov-Szego formula;
  - Bohr-Landau (1914); Selberg;
  - Montgomery (1973); Rudnick-Sarnak; Odlyzko;
  - Hurwitz's theorem; Slepian (prolate spheroidal functions).
