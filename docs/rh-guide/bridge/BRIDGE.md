# The RH-YM bridge: positivity locates singularities, and why 1/2 appears twice

Private working note, 2026-11-23. It follows up items D2 and D5 of `../GUIDE.md` (section 7). Part 1 is a Lean theorem
shared by both projects. Part 2 asks whether the two halves of the RH proof (the mirror and the balance) come from
one duality, as they do in the function-field model. Sources: `../SOURCES.md` (S1 to S9) plus the references in
section 7 below (R1, R2, ...).

**Claim marks** (as in the guide, plus one)

| Mark | Meaning |
|---|---|
| **[Lean-bridge]** | Proved in this repository, `docs/mass-gap/formal/ProofPhase/Bridge/` (Lean 4.34.0, Mathlib v4.34.0, standard axioms only; `axioms.log`). |
| **[Lean]** | Proved in the RH Lean library or in Mathlib; statement read in the source. |
| **[Lean, traced]** | In the RH Lean library according to a community trace (S5, S6); file not re-read by me. |
| **[classical]** | Known mathematics before the RH proof (R-references). |
| **[reading]** | An interpretation, by community readers or by me. |
| **[analogy]** | A structural likeness, not a mathematical result. |
| **[open]** | Not settled, or not checked by anyone I could find. |

---

## 0. The short answer

1. **D5 is now a theorem, not an analogy.** One Lean theorem (`pringsheim_extension`) says: a holomorphic function
   whose Taylor coefficients at real points alternate in sign with non-negative size cannot be continued past the
   real point where its defining series stops converging. Three instances are proved from it: Landau's theorem for
   L-series with non-negative coefficients (the RH proof's stage A), the general Laplace transform of a non-negative
   measure on [0, inf), and the spectral side of the mass gap (decay rate = bottom of the spectrum, and the resolvent
   is singular exactly at the gap). **[Lean-bridge]**
2. **D2 closes only as an analogy.** Over function fields the two halves of the RH have a common source: the
   functional equation comes from Riemann-Roch with Serre duality, and the 1/2 comes out of one positive duality
   (Weil's route: the Hodge index theorem on C x C; equivalently Rosati positivity, FV = q). In Stepanov's elementary
   route, Riemann-Roch is used twice, but the balance's 1/2 is an AM-GM optimum of two degree-linear costs, and the
   coincidence with the mirror's axis is obtained, not explained: a one-sided bound plus the functional equation,
   exactly the architecture of the Lean proof **[classical]**.
3. **The Lean proof's slope step is not arithmetic Riemann-Roch.** On the evidence of the traces, `Frame_at` and its
   neighbours are the arithmetic counterpart of the *zero count* in Stepanov (a non-zero section cannot vanish more
   than its degree allows; over a curve this is "a principal divisor has degree 0", over a number field the product
   formula). Arithmetic Riemann-Roch with its duality (Tate's adelic Poisson summation; van der Geer-Schoof; Bost's
   Poisson-Riemann-Roch) is the counterpart of the *mirror*, and its archimedean part is exactly the Gamma factor
   **[classical]**; in the Lean proof it enters only through Mathlib's functional equation, which is proved by
   Poisson summation for theta functions **[Lean]**.
4. **What is missing for a full bridge:** an arithmetic positivity statement playing the role of the Hodge index
   theorem, from which both the axis of the functional equation and the x/m + m balance would follow. Nothing of the
   kind is on the Lean proof's path, and I know of no such theorem **[open]**.

---

## 1. Part 1: the shared Lean theorem

### 1.1 What was proved

Four modules, 46 theorems, no `sorry`, `admit`, `native_decide` or new axiom; every theorem depends only on
`propext`, `Classical.choice`, `Quot.sound` (`axioms.sh`, `axioms.log`). **[Lean-bridge]**

| Module | Main statements | Content |
|---|---|---|
| `Bridge/Pringsheim.lean` | `pringsheim_hasSum`, `pringsheim_summable`, `glue_differentiableOn`, `pringsheim_extension` | **The shared core.** If `G` is holomorphic on the disc of radius `R` about a real point `c` and `iteratedDeriv n G c = (-1)^n M n` with `M n >= 0`, then `sum M n h^n / n! = Re G(c - h)` for real `0 <= h < R`. Extension form: if `F` is holomorphic on `Re s > x0` with such coefficients at every real `c > x0`, and agrees there with a function holomorphic on a disc about `x0`, then the Taylor series at some `c > x0` converges at a real point `c - h < x0`. |
| `Bridge/Landau.lean` | `landau`, `landau_summable_left`, `landau_ray`, `landau_ray_differentiable` | **Instance A, Landau's theorem.** For `a : N -> C` with `0 <= a` and Mathlib's `LSeries.abscissaOfAbsConv a = x0` real, `LSeries a` has no holomorphic extension to any disc about `x0`. Usable one-sided form: if the series converges somewhere and continues holomorphically around every real `x > theta`, then it converges absolutely, and is holomorphic, on `Re s > theta`. |
| `Bridge/Laplace.lean` | `laplace_landau`, `laplace_conv_left`, `laplace_ray`, `hasDerivAt_lapN`, `iteratedDeriv_lap` | **The general form.** For a measure `mu` on R living on [0, inf), `lap mu s = int e^{-st} dmu(t)`: differentiation under the integral on the half-plane of convergence; if the integral converges for `x > x0` and diverges for `x < x0`, then `x0` is a singularity (Pringsheim-Landau); one-sided form as for L-series. |
| `Bridge/Spectral.lean` | `spectral_gap_iff_nat`, `spectral_gap_iff`, `decayRates_eq`, `resolvent_singular`, `lap_ofReal_eq_corr` | **Instance B, the Yang-Mills side.** For a finite measure `nu` on [0, inf) (the spectral measure of a vector for `H >= 0`) and `corr nu t = int e^{-tE} dnu(E)`: `(exists K, forall n, corr nu n <= K e^{-mn})` iff `nu(Iio m) = 0`, so the admissible decay rates are exactly `{m : nu(Iio m) = 0}` and the best rate is the bottom of the support. With `corrMeasure nu = C(t) dt` on (0, inf): its Laplace integral (classically `<F, (H+s)^{-1} F>`) converges for real `s > -l0`, diverges for `s < -l0`, and by `laplace_landau` has no holomorphic extension about `s = -l0`, where `l0` is the bottom of the support. |

How the two instances use the core: in both, the Taylor coefficient `M n` at a real point `c` is itself a sum (or an
integral) of non-negative terms, `sum_k a_k (log k)^n k^{-c}` or `int t^n e^{-ct} dmu`. The core gives convergence of
`sum_n M n h^n / n!`; the double series has non-negative terms, so it can be summed in the other order (Tonelli),
and the inner sum is `e^{h log k}` or `e^{ht}`. That is convergence of the original series or integral at `c - h`,
beyond where it was supposed to stop. The only analytic input is Cauchy's theorem in Taylor form. The windowed Landau
step of the RH proof works the same way: S5 describes `landau_window` as using "Taylor coefficients at sigma"
**[Lean, traced]**.

### 1.2 What Mathlib already had, and what was added

| Item | Status |
|---|---|
| Taylor series of a holomorphic function on a disc (`Complex.hasSum_taylorSeries_on_ball`) | Mathlib **[Lean]** |
| L-series, abscissa of absolute convergence, derivatives (`LSeries_iteratedDeriv`), abscissa of `logMul` | Mathlib **[Lean]** |
| Sign of the derivatives for non-negative coefficients (`LSeries.iteratedDeriv_alternating`); positivity of a continued L-series on the real axis (`LSeries.positive_of_differentiable_of_eqOn`) | Mathlib **[Lean]**. The second is the nearest Mathlib result to Landau: it uses the same Taylor argument to get a sign, not a singularity. |
| Differentiation under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), exponential series, `lintegral_tsum`, `withDensity` | Mathlib **[Lean]** |
| Absolutely monotone functions (`AbsolutelyMonotoneOn`, citing Widder's *The Laplace Transform*) | Mathlib, definitions and closure properties only; no Bernstein or Landau theorem **[Lean]** |
| Pringsheim's theorem, Landau's theorem, a Laplace transform of measures, abscissas for Laplace integrals, the decay/support equivalence, the resolvent singularity | **Not in Mathlib; added here** **[Lean-bridge]** |

### 1.3 Connection to the repository's OS layer (by name only; nothing imported or edited)

- `ProofPhase.M1.UVTV.RPData.gap_of_RP` (`M1/UVTVOS.lean`) takes as hypothesis `hdec`:
  `Q g (tau^n g) <= C_g e^{-(m n)}` for block observables `g`. Read through the spectral measure `nu_g` of `g` for the
  transfer operator `T = e^{-H}` (which `RPData.T` constructs, symmetric and positive), the left side is
  `corr nu_g n`. `spectral_gap_iff_nat` says this hypothesis holds **if and only if** `nu_g` puts no mass below `m`.
  So `hdec` is exactly a spectral-gap statement for each block observable, and `gap_of_RP` transports it to `F`.
  The shapes match term for term; the identification of `Q g (tau^n g)` with `int e^{-nE} dnu_g(E)` is the spectral
  theorem for the bounded positive operator `T`, which is **[classical]** and not formalized (Mathlib has the
  continuous functional calculus but no spectral measures).
- `ProofPhase.OS.Window`: `WinRP.H x t = Q x (tau^t x)` is the same correlation; `win_decay` and `hankel_cs` are
  log-convexity statements about it, the discrete shadow of "a Laplace transform of a positive measure".

### 1.4 What the theorem does not do

- It locates the **first real** singularity. To exclude all singularities right of `theta` one needs holomorphy along
  the real ray (`landau_ray`, `laplace_ray`). In the RH setting, a real zero beta of L(chi, s) would put a pole on
  that ray. It is excluded by a sign: with the weight `Lambda(n)(x/n - 1)` the explicit formula gives a real zero the
  term `+x^beta / (beta(1 - beta))`, positive, so the Mellin transform of `C x^theta - G(x)` (non-negative) would have
  a pole of negative residue at its abscissa, impossible for a positive measure (my two-line computation from the
  explicit formula, **[classical]**). That is presumably what S5 means by residues that are "positive multiples of one
  number" (`poleData`) **[reading]**. This sign version is **not** formalized here.
- Instance B is abstract: `nu` is any finite measure on [0, inf). Building `nu` from the lattice or continuum measure
  is the OS layer's job.

---

## 2. Part 2, section 1: the function-field model

Let C be a smooth projective curve of genus g over F_q, K its canonical class, l(D) = dim L(D).

**Riemann-Roch with Serre duality** **[classical]** (R1, R2): l(D) - l(K - D) = deg D + 1 - g, and l(K - D) = 0 when
deg D > 2g - 2. Two consequences used below: (a) dimension is degree up to the constant 1 - g, exactly so in large
degree; (b) a non-zero function f has deg div(f) = 0, so it has as many zeros as poles (completeness of the curve,
the function-field product formula).

### 2.1 The mirror: the functional equation from duality

Z(C, t) = sum over effective divisors of t^{deg D} = sum over divisor classes of (q^{l(D)} - 1)/(q - 1) t^{deg D}.
Split the classes by degree. For deg D > 2g - 2 Riemann-Roch gives l(D) exactly and the sum is geometric. For
0 <= deg D <= 2g - 2 the involution D -> K - D on classes, with l(D) - l(K - D) = deg D + 1 - g, pairs degree d with
degree 2g - 2 - d. Together: Z(1/(qt)) = q^{1-g} t^{2-2g} Z(t), i.e. with t = q^{-s}, the completed zeta is symmetric
under s -> 1 - s **[classical]** (R1 ch. 5, R2 ch. 5).

The centre of the symmetry is deg D = g - 1 = deg K / 2: the mirror's axis Re s = 1/2 is **half the canonical class**
(a theta characteristic). In terms of Frobenius eigenvalues, Z = P(t)/((1 - t)(1 - qt)) with P(t) = prod (1 - alpha_i t)
and the functional equation says the multiset {alpha_i} is stable under alpha -> q/alpha **[classical]**.

### 2.2 The balance: Stepanov-Bombieri from Riemann-Roch

Stepanov's method in Bombieri's form (R3; R4 ch. 11; R2 ch. 5) **[classical]**, for q = q0^2 a square:

1. **Existence (dimension count).** Build an auxiliary function from products f^{q0} h with f, h in Riemann-Roch spaces
   L(a P0), L(b P0). Riemann-Roch (consequence (a)) says these spaces have dimension about a and b; the q0-th power
   map is additive and injective, so the products are linearly independent in the needed range, and one can impose
   vanishing at all rational points with high multiplicity while keeping a non-zero function. Serre duality enters
   only through l(K - D) = 0 in large degree, which makes the dimensions exact up to g.
2. **Zero count.** The function vanishes to order about q0 at each of the N rational points (other than P0) and has
   pole order about a q0 + q b (composition with Frobenius multiplies degrees by q). Consequence (b): N q0 <= a q0 + q b.
3. **Balance.** With a, b chosen as small as step 1 allows, this gives N <= q + O(g) q0 + 1: the error is
   (q / q0) + q0 up to constants, smallest at q0 = sqrt(q). Bombieri's bound is N <= q + (2g + 1) sqrt(q) + 1.

The 1/2 here is the AM-GM optimum of two costs that are both **linear in degree**, and they are linear because of
Riemann-Roch (dimension = degree + const) and of deg div(f) = 0. It is the same arithmetic as x/m + m in the Lean
proof (S6) **[Lean, traced]**.

**From the bound to RH, the same architecture as the Lean proof** **[classical]** (R3, R4): the bound is one-sided (an
upper bound on N_r for every extension F_{q^r}); Bombieri gets a lower bound by applying the upper bound to the twists
of a Galois cover (I recall this step from R3 and did not re-read it in this session); the bounds for all r give
|alpha_i| <= sqrt(q) through the radius of convergence of sum_r (sum_i alpha_i^r) t^r; and the functional equation
alpha -> q/alpha gives the reverse inequality. So Stepanov's route also ends with "the right side is empty, the mirror
empties the left": the analogue of `Claim.strip`.

### 2.3 Do both halves come from one duality?

- **The mirror:** yes, Riemann-Roch with Serre duality, fully **[classical]**.
- **The balance in Stepanov's route:** Riemann-Roch is used (dimension count), and Serre duality only through the
  vanishing of l(K - D) in large degree; the exponent 1/2 comes from AM-GM, not from the duality's axis. So in
  Stepanov's route the two 1/2s have a common ingredient (Riemann-Roch) but **different origins** (centre of D -> K - D
  versus geometric mean of q/q0 and q0), and they meet only in the conclusion, as in the Lean proof.
- **Weil's route explains the coincidence** **[classical]** (R5, R6). On the surface C x C, Riemann-Roch gives the
  Hodge index theorem: the intersection form is negative definite on classes orthogonal to the two fibres. Applied to
  the graph of Frobenius it gives the Castelnuovo-Severi inequality, hence |N - q - 1| <= 2g sqrt(q); the square
  root is a Cauchy-Schwarz (discriminant) inequality for that form. Equivalently, on the Jacobian the adjoint of
  Frobenius F for the Weil pairing (Serre duality on H^1) is the Verschiebung V with FV = q, and the Rosati involution
  is positive, which forces alpha * conj(alpha) = q. Here the **mirror** is "dual of F = q / F" and the **balance** is
  "positivity identifies the dual with the complex conjugate": both 1/2s come out of one positive duality.

**Verdict for the function-field model:** the bridge is a theorem in Weil's route (one positive duality) and only a
shared ingredient in Stepanov's route (Riemann-Roch twice, coincidence of axes supplied by the functional equation).

---

## 3. Part 2, section 2: the arithmetic side

### 3.1 Is the slope step arithmetic Riemann-Roch?

What the traces say about the step (S5, the comment "section 5, continued" and the notes around `LinkMu`, `LinkDIV`,
`mu_frac`, `mu_diff`):

- `mu_frac` proves that twisting a Hermitian lattice by a fractional ideal I changes its slope by
  -2 log N(I) / [K : Q], "the slope change from multiplying a Hermitian lattice by a fractional ideal" **[Lean, traced]**.
  This is the finite-place part of the Arakelov degree.
- The lattices N_u are the base lattice enlarged at each place w by the local "gain"; `mu_diff` turns this into an
  exact slope gain, and the arithmetic content (that the gain is genuine p-adic divisibility of theta periods) sits in
  `LinkDIV`, a height bound on the enlarged lattice **[Lean, traced]**.
- S5's own summary: the "degree identity" is "two one-sided comparisons that meet in the middle": the slopes exceed the
  base slopes by the finite-place gains, and the slope inequality plus `DIV` caps them by the archimedean main term
  **[reading]** (S5).

Reading of this evidence **[reading]**: the slope inequality is a statement of the form "finite-place contribution <=
archimedean contribution" for a lattice carrying a non-zero map of bounded height. That is Bost's slope inequality,
whose proof is the product formula applied to a non-zero section (R7, R8, R9). Its function-field counterpart is
step 2 of Stepanov (a non-zero function has no more zeros than poles, deg div(f) = 0), **not** Riemann-Roch.
Stepanov's step 1 (existence by a dimension count, Riemann-Roch's lower bound l(D) >= deg D + 1 - g, or Siegel's lemma
/ Minkowski over number fields) is replaced in the Lean proof by an explicit construction: the chain of m theta lifts
supplies the multiplicity (S3 **[note]**, S5, S6 **[Lean, traced]**). So the counterpart of the Riemann-Roch
*dimension count* is, if anything, the theta-lift construction, and no arithmetic Riemann-Roch theorem has been
identified on the final path **[open]**.

Two near misses, recorded so they are not mistaken for the link:
- S5 lists `idealCharacter_LSeries_continuation`, "built by smoothing, Poisson summation on lattices and a Mellin
  transform" **[Lean, traced]**. This is Hecke's method, the analytic face of Tate's Riemann-Roch. It serves the
  continuation of auxiliary Hecke L-functions (for L(1) != 0), not the slope step; its place on the final path is not
  confirmed in S5 **[open]**.
- The Siegel-Weil formula (`SiegelWeilUnitaryConvergent`, on the path, S5) is ultimately a Poisson-summation identity
  between theta series and Eisenstein series **[classical]**. It feeds near-orthogonality (`LinkS`), not the balance.

### 3.2 Gamma factor = the archimedean part of Arakelov duality?

**Yes, as classical mathematics** **[classical]**:
- Tate's thesis (R10): the completed zeta function is a product of local zeta integrals; the Gamma factor
  pi^{-s/2} Gamma(s/2) is the local integral at the real place with the self-dual Gaussian; the global functional
  equation is Poisson summation on the adeles, which Tate presents as the number-field analogue of Riemann-Roch.
- van der Geer and Schoof (R11): for an Arakelov divisor D they define h^0(D) as the logarithm of a theta sum over the
  ideal lattice with the archimedean metric of D, prove h^0(D) - h^0(kappa - D) = deg D - (1/2) log |Delta| by Poisson
  summation (kappa the canonical Arakelov divisor), and recover the Dedekind zeta function *with its Gamma factors*
  as an integral over the Arakelov class group, whose functional equation follows from that Riemann-Roch. Their theta
  divisor sits at degree (1/2) deg kappa: the arithmetic "half the canonical class". (Abstract confirmed; the formula
  recalled from the paper.) Bost's theta invariants give the same "Poisson-Riemann-Roch" for Euclidean lattices (R12).
- **In the Lean proof:** the mirror step uses Mathlib's `completedLFunction_one_sub`. Mathlib builds the completed
  L-function from Hurwitz zeta functions, whose functional equation comes from the Jacobi theta function's, proved
  "using Poisson's summation formula" with a Gaussian (`JacobiTheta/TwoVariable.lean`); the Gamma factor is the
  definition `gammaFactor`, documented as "The Archimedean Gamma factor" **[Lean]** (Mathlib). So the mirror in the
  final proof is, concretely, arithmetic Riemann-Roch in Tate's sense, with the archimedean place supplying the Gamma
  factor.

The archimedean place also enters the balance: the main term `MAIN` is a mean of log-periods of CM elliptic curves,
turned into L'/L(1, chi) by Chowla-Selberg and the Kronecker limit formula (`mean_log_period`, `meanPeriod`)
**[Lean, traced]**. Chowla-Selberg is the archimedean (Faltings-height) side of the arithmetic degree of CM points
**[classical]** (R13). So both halves have an archimedean term, the Gamma factor in the mirror and the period in the
balance, and both terms descend from theta and Eisenstein series **[classical]**. That they are the same duality's
archimedean part is **[reading]**: no statement on the path links them.

---

## 4. Verdict, link by link

| Link | Status | Evidence / what is missing |
|---|---|---|
| D5: positivity plus a one-sided bound locates singularities (Landau for L-series; spectral gap = decay rate; resolvent singular at the gap) | **proved** | `pringsheim_extension`, `landau`, `laplace_landau`, `spectral_gap_iff_nat`, `resolvent_singular` **[Lean-bridge]** |
| D5 applied to the RH proof's stage A | **proved in form, not instantiated** | `landau_ray` is the shape of stage A; the RH library's own `landau_window` is a windowed variant with the same Taylor-coefficient method (S5) **[Lean, traced]**. Exclusion of real zeros by residue sign: **sketched** (section 1.4), not formalized. |
| D5 applied to the YM proof | **proved in form, link by name** | `spectral_gap_iff_nat` matches `gap_of_RP`'s `hdec` term for term; spectral measure of `T = e^{-H}` **[classical]**, not formalized. |
| Function fields: functional equation from Riemann-Roch + Serre duality | **classical (sketched here)** | section 2.1 (R1, R2) |
| Function fields: Stepanov's balance from Riemann-Roch | **classical (sketched here)**, with the caveat that the 1/2 is AM-GM, not the duality axis | section 2.2 (R3, R4) |
| Function fields: one duality gives both 1/2s | **classical in Weil's route** (Hodge index / Rosati positivity), **not** in Stepanov's | section 2.3 (R5, R6) |
| Arithmetic: slope step = arithmetic Riemann-Roch | **no, on present evidence**; it is the counterpart of the zero count (product formula) **[reading]** | section 3.1 (S5); the counterpart of the dimension count is the theta-lift construction **[reading]** |
| Arithmetic: Gamma factor = archimedean part of arithmetic duality | **classical**; and the Lean mirror is proved this way in Mathlib **[Lean]** | section 3.2 (R10, R11, Mathlib) |
| Arithmetic: mirror axis and balance point coincide for one reason | **open** | Missing step: an arithmetic positivity theorem playing the role of the Hodge index on C x C (a positive pairing whose adjoint relation is s -> 1 - s), from which the x/m + m balance would follow. The Lean proof gets the two 1/2s separately (stage C and stage 0). |

**Where the bridge stands.** Between the two projects the bridge is a theorem: both use the same Pringsheim-Landau
lemma, now proved once in Lean. Inside the RH proof, the "why 1/2 twice" bridge closes only as an analogy: over
function fields there is a theorem (Weil's positivity) explaining the coincidence, but the Lean proof follows
Stepanov's route, where the coincidence is obtained, not explained. The exact missing step is named in the last row.

**A side remark across projects [analogy].** In Weil's route the mirror and the positivity are one structure (a
positive form built from an adjoint: Rosati, or the Hodge index). That is the shape of Osterwalder-Schrader reflection
positivity (a positive form <theta F, F> built from the time reflection). The RH proof, like Stepanov, keeps mirror and
positivity apart (guide, section 3(a)); the YM proof joins them, as Weil does. This is why the shared lemma of Part 1
sits on the positivity side only.

---

## 5. DMP readings (separate; not mathematics)

> **This section maps the owner's DMP readings (`docs/mass-gap/weak-coupling/PREP.md`) onto the structures above.
> Nothing here is a mathematical result; each item says what is exact, what is analogy, and what does not fit.**

**Inversion and halving.** Every 1/2 in this note is the fixed point of an inversion: s -> 1 - s (axis 1/2),
alpha -> q/alpha (circle sqrt(q)), D -> K - D (degree g - 1, half of K), m -> x/m (balance at sqrt(x)), q0 -> q/q0
(Stepanov). "Halving" is in each case the geometric mean of a pair and its inverse partner. *Exact* as a description of
these formulas; *analogy* as a claim that they are one phenomenon. Section 2.3 says when it is one phenomenon: over
function fields in Weil's route, where the inversion is a duality and positivity selects its fixed set.

**Duality.** Serre duality (K - D), Poisson summation (Tate, van der Geer-Schoof, Mathlib's theta functional equation)
and OS time reflection are three dualities in this note. The first two are the same duality in the classical
dictionary (R10, R11), *exact correspondence*. The third is a different mathematical object; its likeness to Weil's
positivity (section 4, side remark) is an *analogy*.

**The gap as a binary result.** `spectral_gap_iff_nat` splits the real line at one point: below the bottom of the
spectrum every rate m has "no mass below m", above it every rate fails. The admissible rates form a down-set whose
supremum is the gap (`decayRates_eq`), a two-sided cut in Dedekind's sense. Landau's theorem has the same binary shape:
at each real point the series either converges or has met its singularity, with nothing in between on the real axis.
*Exact correspondence* in logical form (the statements are dichotomies at a cut); *analogy* for any reading beyond that.

**Duality proves the result?** *Does not fit* the RH proof (guide D1) and does not fit Part 1 either: the shared
lemma uses positivity alone, no reflection.

---

## 6. Files

- `docs/mass-gap/formal/ProofPhase/Bridge/Pringsheim.lean`, `Landau.lean`, `Laplace.lean`, `Spectral.lean`
- `docs/rh-guide/bridge/axioms.sh` (build plus `#print axioms` for all 46 theorems plus a source grep) and its output
  `axioms.log`
- Build: from `docs/mass-gap/formal`, `FORMAL_DST=<folder> bash sync-build.sh ProofPhase.Bridge.<Module>` in the WSL
  replay distro; 0 warnings for all four modules.

---

## 7. References (standard literature; no files downloaded)

- **R1.** M. Rosen, *Number Theory in Function Fields*, Springer GTM 210 (2002), ch. 5: zeta functions of function
  fields, rationality and functional equation from Riemann-Roch.
- **R2.** H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Springer GTM 254 (2009), ch. 1 (Riemann-Roch)
  and ch. 5 (zeta function, functional equation, Hasse-Weil bound).
- **R3.** E. Bombieri, "Counting points on curves over finite fields (d'apres S. A. Stepanov)", Seminaire Bourbaki
  exp. 430 (1972/73), Lecture Notes in Math. 383 (1974).
- **R4.** H. Iwaniec, E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publ. 53 (2004), ch. 11 (sums over finite
  fields, Stepanov's method).
- **R5.** A. Weil, *Sur les courbes algebriques et les varietes qui s'en deduisent* (1948); *Varietes abeliennes et
  courbes algebriques* (1948).
- **R6.** R. Hartshorne, *Algebraic Geometry*, Springer GTM 52 (1977), V.1 (Hodge index theorem, exercise on the
  Riemann hypothesis for curves via Castelnuovo-Severi); D. Mumford, *Abelian Varieties* (1970), section 21 (Rosati
  positivity and the Riemann hypothesis).
- **R7.** J.-B. Bost, "Periodes et isogenies des varietes abeliennes sur les corps de nombres", Seminaire Bourbaki
  exp. 795 (1994/95), Asterisque 237 (1996): the slope inequality.
- **R8.** J.-B. Bost, "Algebraic leaves of algebraic foliations over number fields", Publ. Math. IHES 93 (2001).
- **R9.** E. Gaudron, "Pentes des fibres vectoriels adeliques sur un corps global", Rend. Sem. Mat. Univ. Padova 119
  (2008); H. Chen, A. Moriwaki, *Arakelov Geometry over Adelic Curves*, Lecture Notes in Math. 2258 (2020).
- **R10.** J. Tate, "Fourier analysis in number fields and Hecke's zeta-functions" (thesis, 1950), in Cassels-Froehlich
  (eds.), *Algebraic Number Theory* (1967): section 4.2, the Riemann-Roch theorem as adelic Poisson summation.
- **R11.** G. van der Geer, R. Schoof, "Effectivity of Arakelov divisors and the theta divisor of a number field",
  Selecta Math. (N.S.) 6 (2000) 377-398 (arXiv math/9802121); abstract checked 2026-11-23.
- **R12.** J.-B. Bost, *Theta Invariants of Euclidean Lattices and Infinite-Dimensional Hermitian Vector Bundles over
  Arithmetic Curves*, Progress in Math. 334, Birkhaeuser (2020).
- **R13.** S. Chowla, A. Selberg, "On Epstein's zeta-function", J. reine angew. Math. 227 (1967); P. Colmez, "Periodes
  des varietes abeliennes a multiplication complexe", Ann. of Math. 138 (1993).
- **R14.** E. Landau, "Ueber einen Satz von Tschebyschef", Math. Ann. 61 (1905) (Landau's theorem); A. Pringsheim (1894)
  and D. V. Widder, *The Laplace Transform* (1941), ch. II (the Laplace-transform form). Used for Part 1's statements.
