# GRH along the positivity route: a time-boxed attempt

Private working note, 2026-11-23. The owner's reading (PREP.md, entry "Positivity is the corollary 'something
exists'"): a positive pairing builds a Hilbert space; in it the reflection becomes self-adjoint; a self-adjoint
operator has real spectrum; real spectrum means every zero is on the line. The step from positivity to the line is
known (Weil's criterion). The target here is the positivity itself, modelled on how the Yang-Mills proof gets
reflection positivity. The rule was to stop at the first step that cannot be closed and to name it exactly.

**Claim marks** (as in `../GUIDE.md`)

| Mark | Meaning |
|---|---|
| **[Lean-grh]** | Proved in `docs/mass-gap/formal/ProofPhase/GRH/Weil.lean` (standard axioms only; `axioms.sh`, `axioms.log`). |
| **[Lean-bridge]** | Proved in `ProofPhase/Bridge/` (earlier steps). |
| **[numerical]** | Computed by `weil_numerics.py` (CPU, about 3 minutes; output `weil_numerics.log`). |
| **[classical]** | Known mathematics (references in section 7). Items recalled from the literature rather than re-read in this session say so. |
| **[proved here]** | A short argument written out in this note, not in Lean. |
| **[reading]** | An interpretation. |
| **[open]** | Not settled. |

---

## 0. Where it stops

- **a. Weil's criterion in Lean.** Proved in full in a finite model (finitely many zeros): positivity of the zero
  pairing holds **iff** every zero is on the line **[Lean-grh]**. The general direction "positivity implies the line"
  is also proved in Lean, but only for test classes with an approximation property, which is stated as a named
  hypothesis. For actual Dirichlet L-functions, two inputs are missing from Mathlib: the explicit formula, and a
  zero-counting bound (needed for the approximation property).
- **b. The pairing modelled on reflection positivity** turns out to *be* Weil's pairing. The OS restriction to
  positive times is empty here, because the pairing is translation invariant. The real difference from Yang-Mills is
  Toeplitz against Hankel positivity: real-time against Euclidean.
- **c. Numerically, positivity holds everywhere it can be resolved, but with no room.** The smallest eigenvalue of
  the Weil form on test functions supported in [-a, a] falls from 0.24 (a = 0.15) to about 3e-9 (a = 0.7). Beyond
  a = 1 it sits below 1e-10, at the limit of double-precision quadrature. Every apparent negative value shrinks
  towards zero when the accuracy is raised **[numerical]**.
- **d. The paper attempt stops at step 4.** Positivity is provable while the test functions are too short to see a
  prime **[classical]**. To get past the first prime one needs a positive object, defined from arithmetic data and not
  from the zeros, whose reflection pairing is Weil's form. The only positive arithmetic object available (the Euler
  product's measure on the logarithms of prime powers, the one Landau's argument uses) enters Weil's form with the
  **wrong sign**. That step is equivalent to GRH itself **[open]**.

---

## 1. The chain, and which link is which

1. **Positivity gives a Hilbert space.** A positive semidefinite pairing <f, g> on a vector space, completed after
   dividing out the null vectors, is a Hilbert space (the GNS construction) **[classical]**. The repository does
   exactly this for reflection positivity: `RPData.Pre` and `RPData.H` in `M1/UVTVOS.lean` **[Lean]** (repository).
2. **The reflection, or translation, becomes self-adjoint there; its spectrum is real** **[classical]**.
3. **Real spectrum means the zeros are on the line.** With rho = 1/2 + i gamma, "gamma real" is "Re rho = 1/2".
   Weil's criterion makes this precise: GRH for chi holds iff W_chi(f * f~) >= 0 for all test functions f
   **[classical]** (Weil 1952; Bombieri 2000).

Links 1 to 3 are the known direction. In the finite model it is now a theorem in Lean (section 2). The open link is
the positivity at the start.

---

## 2. Step a: Weil's criterion in Lean

**Set-up.** Write each zero of L(chi, s) in the strip as rho = 1/2 + i gamma. For a single chi, the functional
equation combined with complex conjugation sends rho to 1 - conj(rho), which is gamma -> conj(gamma) **[classical]**.
For a test function f on the line (log scale), let F(z) = int f(x) e^{izx} dx and f~(x) = conj f(-x). Then h = f * f~
has transform F(z) conj F(conj z), and the zero side of Weil's functional is

  W(F) = sum over zeros of F(gamma) conj F(conj gamma)          (`weilSum`, indexed with multiplicity).

The explicit formula equates this with an arithmetic side (section 3).

**Proved [Lean-grh]:**

| Theorem | Statement |
|---|---|
| `weilSum_re_nonneg_of_real` | If every gamma is real (GRH), then Re W(F) >= 0 for every F. Each term is \|F(gamma)\|^2. |
| `real_of_weilSum_nonneg` | **Positivity implies GRH**, for any test class with the approximation property. The approximation property: for every finite set S of zeros (saturated: all copies of a zero together), every target r and every eps > 0, some test transform equals r on S while the rest of the zero sum has size at most eps. Proof: if gamma_0 were not real, take F = 1 at gamma_0, -1 at conj(gamma_0), and 0 at the other zeros of S. Each of the at least two terms over S is -1, so Re W <= -2 + eps < 0. |
| `approx_finite` | In a finite model the approximation property holds **exactly** for finite exponential sums F(z) = sum c_k e^{i z x_k} (transforms of finite combinations of point masses). The proof is Lagrange interpolation in w = e^{i z eps}; `exists_step_injOn` chooses eps so that w separates the zeros. |
| `weil_criterion_finite` | **Finite model: the zero pairing is non-negative on all finite exponential sums iff every zero is on the line.** |

**Did the bridge help?** No, and the reason is informative. The bridge's lemma (Pringsheim-Landau) is Hankel (Laplace)
positivity: a positive measure, real exponents, singularities on a real axis. Weil's direction is Toeplitz
(Fourier) positivity. Its natural theorem is Bochner's (a positive-definite function is the Fourier transform of a
positive measure on the real line). The finite-model proof is the elementary core of Bochner's argument (interpolate,
then evaluate). Section 3 explains why the two kinds of positivity sit on opposite sides of the explicit formula.

**Missing for actual Dirichlet L-functions:**
1. **The explicit formula** for L(chi, s), equating W(F) with the arithmetic side, for a test class (e.g. smooth
   compactly supported f). Mathlib has the completed L-function and its functional equation, but no explicit formula
   **[Lean]** (searched). The RH library has `explicit_formula_dirichlet_zeros_right_half`, a truncated form over the
   zeros right of 1/2 (guide, section 5; statement read there, not here).
2. **The approximation property** for smooth compactly supported test functions with infinitely many zeros. It needs
   the zero count N(T) = O(T log T), so that the tail of the zero sum can be controlled, and a Paley-Wiener
   construction of test functions with prescribed values at finitely many zeros **[classical]**. Neither is in
   Mathlib.
3. **The symmetry gamma -> conj(gamma)** of the zeros, from `completedLFunction_one_sub` and conjugation. This is
   close to Mathlib and not done.

---

## 3. Step b: the pairing modelled on reflection positivity

**The arithmetic side.** For chi primitive mod q, of parity k (0 even, 1 odd), and h = f * f~ **[classical]**,
checked numerically to 1e-16 for zeta (section 4):

  W_chi(f) = [zeta only: F(i/2) F(-i/2) + F(-i/2) F(i/2)]
             + h(0) log(q/pi) + (1/2pi) int |F(r)|^2 Re psi(k/2 + 1/4 + ir/2) dr
             - sum_n Lambda(n) n^{-1/2} [chi(n) h(log n) + conj chi(n) h(-log n)].

The middle line is the real place: it is the logarithmic derivative of the Gamma factor (`gammaFactor` in Mathlib).
The last line is the finite places.

**The candidate pairing.** Take the reflection theta f(x) = conj f(-x). On the log scale, after the normalisation by
x^{1/2}, this is s -> 1 - s on the critical line. Define <f, g>_W = W_chi(f * theta g), with the Gamma factor as the
real place. The statement that would make it positive is

  **P(chi, a): W_chi(f * f~) >= 0 for every smooth f supported in [-a, a].**

GRH for chi holds iff P(chi, a) holds for every a **[classical]** (Weil). Two observations:

1. **The OS half-space is empty here** **[proved here]**. Reflection positivity asks <theta F, F> >= 0 only for F
   supported at positive times. W depends on f only through h = f * f~, and h does not change when f is translated.
   Every compactly supported f can be translated into (0, inf), so the half-space condition is no condition: RP with
   theta = (x -> -x) for this pairing *is* Weil positivity.
2. **Hankel against Toeplitz** **[classical]**, with the reading **[reading]**:
   - OS reflection positivity on a time line is Hankel positivity, sum conj(c_i) c_j C(t_i + t_j) >= 0 for t_i > 0.
     It forces C(t) = int e^{-tE} dnu(E) with nu >= 0 (Bernstein-Widder): a Laplace transform with real energies.
     This is the bridge's setting, `Spectral.lean`.
   - Weil positivity is Toeplitz positivity, sum conj(c_i) c_j W(x_i - x_j) >= 0. It forces W to be the Fourier
     transform of a positive measure (Bochner): real frequencies gamma.
   - In Yang-Mills the two are linked by the Wick rotation: Euclidean RP gives H >= 0, and then the real-time
     correlations are positive definite. On the arithmetic side the positive Hankel object exists, but on the *prime*
     side. log L(s) = sum Lambda(n) chi(n) / (log n) n^{-s}; for zeta its coefficients are non-negative. So this is the
     Laplace transform of the positive measure sum Lambda(n)/log n delta_{log n}, whose "energies" are the logarithms
     of prime powers. This is the positivity Landau's argument and the RH Lean proof use.

---

## 4. Step c: numerical test

`weil_numerics.py`, CPU, about 3 minutes; output in `weil_numerics.log` **[numerical]**.

**Normalisation check.** For zeta with Gaussian test functions (widths 0.25, 0.4, 0.6), the zero side (150 zeros) and
the arithmetic side agree to 7e-17, 8e-16 and 3e-16. So the formula in section 3 is right.

**The smallest eigenvalue.** Take the 10-dimensional space spanned by (1 - t^2)^2 P_j(t), t = x/a, with P_j the
Legendre polynomials, so the functions are supported in [-a, a]. lambda_min = min W(f) / int f^2 over that space,
computed from the arithmetic side only (no zeros used). It is then compared with the zero side of the minimiser.

| a | prime powers seen (n <= e^{2a}) | zeta: lambda_min | zeta: zero side of minimiser | chi_4: lambda_min |
|---|---|---|---|---|
| 0.15 | none | 2.38e-1 | 2.38e-1 | 1.21 |
| 0.25 | none | 4.16e-2 | 4.16e-2 | 7.48e-1 |
| 0.3466 = (log 2)/2 | 2 (at the edge) | 1.94e-3 | 1.94e-3 | 4.66e-1 |
| 0.45 | 2 | 3.41e-5 | 3.41e-5 | 2.53e-1 |
| 0.7 | 2, 3, 4 | 2.6e-9 | 2.5e-9 | 1.07e-2 |
| 1.0 | 5 | below 1e-10 (noise) | 2.6e-11 | 4.4e-6 |
| 1.5 | 12 | below 1e-10 (noise) | 3.7e-11 | 6.4e-9 |
| 2.0, 2.5 | 24, 47 | noise level | noise level | noise level |

(For chi_4 the first prime that counts is 3, since chi_4(2) = 0.)

**Accuracy check.** At a = 1.0 and 1.5 the coarse runs gave values down to -1.1e-8. Doubling the quadrature nodes
and quadrupling the frequency grid and cut-off moved them to -3.9e-11 and +2.5e-12, against zero-side values +2.6e-11
and +3.7e-11. With 6 basis functions instead of 10 the margins are larger, and the two sides agree to three digits:
7.18e-8 against 7.23e-8 at a = 1; 4.16e-10 against 3.93e-10 at a = 1.5. **No violation was seen. The negative values
are quadrature error.**

**Where it is tight.** The minimiser is a test function whose transform almost vanishes at the low zeros: its value
of W is exactly the weight of the zeros it cannot avoid (column 4 equals column 3). With support [-a, a] and N basis
functions, such functions get better super-exponentially as a and N grow, much like prolate spheroidal functions. So
the positivity margin collapses super-exponentially. This matches the very small eigenvalues reported by Connes and
Consani for the Weil form on growing intervals (recalled, not re-read). For a proof this means **no estimate with any
loss can work**: positivity has to come out as an exact identity (a norm squared), not as an inequality with error
terms. This is the opposite of the RH Lean proof's situation, where a one-sided bound with x^eps losses was enough.

---

## 5. Step d: the paper attempt, step by step

1. **Split W into places:** W_chi = W_pole + W_inf + W_fin, as in section 3. **[classical]**
2. **Short test functions see no prime.** If f is supported in [-a, a] and 2a < log n_1, where n_1 is the first prime
   power with chi(n_1) != 0, then h = f * f~ vanishes at every +-log n and W_fin(f) = 0 **[proved here]** (support of
   a convolution).
3. **Positivity without primes.** W_pole + W_inf >= 0 for such short f. For zeta this is the theorem of Yoshida (1992)
   and Connes-Consani (2021), for supports up to about (log 2)/2 on the log scale (recalled, not re-read)
   **[classical]**. Numerically: 0.24 and 0.042 at a = 0.15 and 0.25 for zeta; 1.21 and 0.75 for chi_4
   **[numerical]**. This is the only range where positivity is a theorem.
4. **Past the first prime: needs a positive object.** For longer f the prime terms enter with a minus sign, each term
   indefinite in f. Following the Yang-Mills model, one would write W(f * f~) = \|Phi f\|^2. Here Phi maps test
   functions into a Hilbert space, *defined from arithmetic data without reference to the zeros*. In Yang-Mills, Phi
   comes from a positive weight (e^{-S} >= 0) plus locality (the action splits across the reflection plane), so
   <theta F, F> = int \|int F e^{-S_+}\|^2 >= 0. Candidates checked:
   - **The zero side itself:** gives Phi, but uses the zeros, so it is circular (it is GRH). **[proved here]**
   - **Place by place (locality):** W_inf is positive only for short support, and each prime term is indefinite. A
     sum of local pieces does not give positivity term by term; in the Yang-Mills dictionary the "action" is not
     real. **[proved here]** for indefiniteness (a single term -c [h(u) + h(-u)] takes both signs on f * f~);
     **[reading]** for the dictionary.
   - **The Euler product's positive measure** (section 3, observation 2): positive, Hankel, with the logarithms of
     prime powers as energies. It is exactly what Landau's argument (bridge, Part 1) and the RH Lean proof use. But it
     enters Weil's form with a **minus** sign: the explicit formula carries the positive prime-side measure to the
     zero side with the wrong orientation. The Yang-Mills analogue would be a Boltzmann weight e^{+S}. **[reading]**,
     with the sign **[classical]**.
   - **Connes's trace formula on the adele class space:** W is the trace of an operator there, and the positivity is
     an open problem **[classical]** (Connes 1999, recalled), **[open]**.

**The step that cannot be closed (named as precisely as the bridge's missing step):**

> **Step 4.** Construct a Hilbert space H_chi and a linear map Phi from smooth compactly supported test functions to
> H_chi, defined from arithmetic data alone (primes, characters, the real place) and not from the zeros, such that
> <Phi f, Phi g> = W_chi(f * g~) for all test functions with support longer than log n_1. By Weil's criterion together
> with the GNS construction, such a Phi exists iff GRH holds for chi. So this step is the conjecture itself, in
> Hilbert-space form. No partial version is known beyond the prime-free range of step 3, and section 4 shows any
> construction must be exact (no loss), because the margin collapses super-exponentially. **[open]**

**Why the RH Lean proof did not need this step** **[reading]**: it never uses Weil's two-sided form. It uses the
prime-side Hankel positivity one-sidedly (Landau: a one-sided bound pushes singularities left) and gets the bound
from a Stepanov balance. The positivity it needs is the kind that exists (guide, section 3(a)). The positivity route
asks for the kind that does not yet exist.

---

## 6. DMP readings (separate; not mathematics)

> **This section maps the owner's readings (PREP.md, "Positivity is the corollary 'something exists'" and the G0
> remark) onto the attempt. Nothing here is a mathematical result.**

- **"Something has to exist, otherwise nothing about it would be describable."** *Exact correspondence* with the GNS
  step: without a positive pairing there is no Hilbert space, no operator and no spectrum to describe (section 1;
  `RPData.H` in the repository is this construction). In the finite model, "existence forces the line" is a theorem
  (`weil_criterion_finite`).
- **"Once we force existence, which in GRH can only be on the prescribed line."** *Exact correspondence* for the
  direction positivity => line (section 2). The forcing itself is step 4, which is open.
- **Press to G0 before use.** *Analogy* for the order: positivity first, then the space, then the spectrum. In
  Yang-Mills the measure's positivity (e^{-S} >= 0) is given by construction and locality turns it into RP. For GRH
  the given positive weight (the Euler product) points the wrong way in Weil's form, so "the system holds" has not
  yet been established on the side where it is needed.
- **Two positivities, two sides.** *Reading*: the arithmetic world has a positive "Euclidean" object (primes, Hankel,
  Landau) and needs a positive "real-time" object (zeros, Toeplitz, Weil). The explicit formula is the Wick rotation
  between them, and it does not carry positivity across. In Yang-Mills OS reconstruction does carry it across,
  because H >= 0. Whether some arithmetic analogue of "H >= 0" exists is the open question in another dress.

---

## 7. Files and references

**Files.** `docs/mass-gap/formal/ProofPhase/GRH/Weil.lean` (5 theorems, standard axioms, 0 warnings);
`docs/rh-guide/grh/axioms.sh`, `axioms.log`; `weil_numerics.py`, `weil_numerics.log`.

**References.**
- A. Weil, "Sur les 'formules explicites' de la theorie des nombres premiers", Comm. Sem. Math. Univ. Lund (1952):
  the explicit formula and the positivity criterion.
- E. Bombieri, "Remarks on Weil's quadratic functional in the theory of prime numbers I", Rend. Mat. Acc. Lincei
  (9) 11 (2000).
- H. Yoshida, "On Hermitian forms attached to zeta functions", Adv. Stud. Pure Math. 21 (1992) (positivity for small
  support; recalled).
- A. Connes, "Trace formula in noncommutative geometry and the zeros of the Riemann zeta function", Selecta Math. 5
  (1999); A. Connes, C. Consani, "Weil positivity and trace formula, the archimedean place", Selecta Math. 27 (2021)
  (recalled).
- H. Iwaniec, E. Kowalski, *Analytic Number Theory* (2004), section 5.5 (explicit formula, the form used in section 3);
  Z. Rudnick, P. Sarnak, Duke Math. J. 81 (1996) (same normalisation).
- K. Osterwalder, R. Schrader, Comm. Math. Phys. 31 (1973), 42 (1975): reflection positivity and reconstruction;
  S. Bochner (positive-definite functions); D. V. Widder, *The Laplace Transform* (1941): Bernstein's theorem and
  Hankel positivity.
