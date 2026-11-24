# The reductio through the locally evaluable functional equation (Tate's thesis)

Private working note, 2026-11-23. It follows `VARIATIONAL.md` and the faces before it (`ATTEMPT.md` step 4,
`LEE-YANG.md`, `ORBITS.md`, `INDUCTION.md`). The question comes from the owner's reading in PREP.md ("The best
approach: the functional equation, proven to be locally evaluable"): "the link to G0 is literally the functional
equation proven to be locally evaluable".

The tasks:
1. state Tate's form;
2. try the reductio: assume an off-line pair rho, 1 - conj(rho), and use only the local data and the global Poisson
   identity;
3. ask whether Tate's local freedom lets positivity be assembled place by place.

As before, RH is proved (Lean) elsewhere in this repository, so the question is the mechanism, not the truth.

**Claim marks** are as in `INDUCTION.md`:
- **[numerical]** = `tate.py` (output `tate.log`, 13 s), on the grid of `induction.py`;
- **[classical]** = known; "recalled" means recalled, not re-read in this session; "abstract" means only the abstract
  was read;
- **[proved here]** = argued in this note, on paper unless it says Lean;
- **[Lean]** = `ProofPhase/GRH/Tate.lean`, 6 theorems, standard axioms only (`axioms-tate.log`);
- **[Mathlib]** = a theorem of the Mathlib version pinned by the repository, cited by name;
- **[reading]** = interpretation;
- **[open]** = not settled.

---

## 0. The answers

1. **Tate's form is exactly "the functional equation, locally evaluable".**
   - The completed zeta function is a product of local zeta integrals, one per place.
   - Each place has its own functional equation, whose factor is independent of the test function.
   - That factor is a pure phase on the critical line. Lean proves this for every unramified prime.
   - The global functional equation is Poisson summation for Q inside the adeles.
   - Mathlib proves the same equation by the same mechanism: theta and Poisson at the real place, Mellin transform,
     and the archimedean factor `Gammaℝ`.
2. **The reductio cannot be done with the functional equation alone, and the failure is exact.**
   - Every local factor is zero-free, so the zeros are created only by the global Poisson identity.
   - That identity is linear in the test function. Mathlib proves the functional equation for **every** even or odd
     function on Z/N, not only for characters (`ZMod.completedLFunction_one_sub_even` / `_odd`).
   - Among those functions is the Davenport-Heilbronn combination mod 5. It has the same kind of self-dual functional
     equation, but it has zeros off the line (recalled).
   - So local functional equations + global Poisson + the Gaussian allow an off-line pair. This is the arithmetic
     instance of `krein_off_line`.
3. **What has to be added is a sign, and there is exactly one local sign available.**
   - The local sign is Lambda(n) >= 0: each Euler factor's log-derivative has nonnegative coefficients.
     Davenport-Heilbronn lacks it.
   - With Landau's theorem, that local sign turns a **one-sided** square-root bound on psi(x) - x into the
     contradiction with an off-line pair (`INDUCTION.md` section 3).
   - The one-sided bound itself is global. It does not follow from the local data plus Poisson, and generalised-prime
     systems with regular integers violate it (Diamond-Montgomery-Vorhauer).
4. **Positivity cannot be assembled place by place in Weil's form.** Lean and the numbers together show it:
   - **Only the lag-0 part can be exchanged:** different primes live on disjoint lattices k log p (unique
     factorisation, Lean), so places can exchange only the lag-0 (identity) part.
   - **Each prime block is indefinite:** it has zero diagonal, which makes it indefinite as soon as it is non-zero
     (Lean).
   - **So the real place would have to be positive on its own:** place-by-place positivity forces the real place's
     own form to be positive and to pay for every prime (Lean).
   - **The numbers:** the real place loses positivity at support 0.40 to 0.43, just after the prime 2 enters at
     (1/2) log 2 = 0.347. By support 1.225 the place-by-place condition fails by 9.7 t_0, while the whole form is
     positive by 1e-9 t_0.
   - **Tate's freedom does not touch this:** it acts on the zeta integrals, not on Weil's local distributions, which
     are canonical.
5. **"It runs" as the formal target (section 2a).** The owner's answer to "what positivity the reductio needs on
   top of the functional equation" was: "It runs."
   - **The construction:** the scaling flow on the completion of test functions in Weil's form.
   - **What it gives for free:** the flow preserves the form automatically.
   - **The reductio, in this form:** if the flow does not increase a positive norm, there is no growing mode. The
     functional equation pairs every decaying mode with a growing one, so every mode is a phase, which is RH
     (`runs_and_mirror_on_line`, Lean; `atoms_on_circle` in grid form).
   - **The open part:** that norm is Weil's form, and its positivity is the open step. In the constructions where the
     norm is positive by construction, the space either does not see the off-line zeros (Connes's L^2 of the
     adele class space) or yields only a half-plane (Lax-Phillips).
   - **Where positivity would have to come from:** it would have to survive the quotient by the rationals (the
     Poisson step). Tate's local norms are positive, but the quotient is where the zeros appear, and positivity is
     not inherited there for free.
6. **The stop.** The sign is global: an inequality that couples every place up to the scale at once. In Weil's form
   it is positivity, which only the full cancellation between places achieves; in the "runs" form it is the
   positivity of the norm in which the scaling flow runs. In Dirichlet form it is the one-sided square-root prime
   bound, which Landau completes using the local sign Lambda(n) >= 0. This is the seventh face of the one obstacle
   (section 6).

---

## 1. Tate's form

**Local zeta integrals [classical, recalled: Tate 1950].** For a place v of Q, a Schwartz-Bruhat function f_v on
Q_v and Re s > 0, set Z_v(f_v, s) = integral over Q_v^x of f_v(x) |x|_v^s d^x x, using self-dual measures and the
standard additive character.

| place | standard f_v | Z_v(f_v, s) = local factor L_v(s) | local gamma factor gamma_v(s) = Z_v(f^_v, 1 - s) / Z_v(f_v, s) |
|---|---|---|---|
| p (unramified) | 1 on Z_p | (1 - p^-s)^-1 | (1 - p^-s) / (1 - p^(s-1)) |
| real | e^(-pi x^2) (self-dual) | pi^(-s/2) Gamma(s/2) = `Gammaℝ s` | Gammaℝ(1 - s) / Gammaℝ(s) |

- **Local functional equation:** Z_v(f^_v, 1 - s) = gamma_v(s) Z_v(f_v, s) for **every** f_v, with gamma_v
  independent of f_v. This is the functional equation evaluated at one place.
- **Each gamma_v is a phase on the line:**
  - At p: |gamma_p(1/2 + i t)| = 1, because p^(s-1) is the conjugate of p^(-s) there (`local_factor_unimodular`,
    **[Lean]**).
  - At the real place: Gammaℝ(1/2 - i t) is the conjugate of Gammaℝ(1/2 + i t).
  - So each local Fourier transform acts on the critical line as a unitary multiplier. This is the local form of the
    unitary scaling action of `INDUCTION.md` section 1a.
- **Global:** for f = (product of the f_v), Z(f, s) = integral over the ideles of f(x) |x|^s d^x x = the product of
  the Z_v, for Re s > 1.
  - With the standard f this is Lambda(s) = Gammaℝ(s) zeta(s).
  - Poisson summation for Q in the adeles (sum over Q of f(q x) = |x|^-1 times the sum over Q of f^(q / x)) gives
    the continuation and Z(f, s) = Z(f^, 1 - s), up to the two pole terms at s = 0 and s = 1.
  - The product of the gamma_v is 1.
- **Tate's freedom:** replacing f_v by another local function multiplies Z by Z_v(f_v, s) / L_v(s). That ratio is
  entire: a Laurent polynomial in p^-s at p, and an entire function at the real place. L_v is the "gcd" of the local
  integrals. So **the zeros of zeta are the common zeros of all Z(f, s)**: Tate's freedom can add zeros, never move
  zeta's.

**The in-repo anchor [Mathlib]:**
- **The local factors:**
  - `Gammaℝ` (`Analysis/SpecialFunctions/Gamma/Deligne.lean`) is the real place's local factor.
  - `riemannZeta_eulerProduct_tprod` is the product of the finite local factors (1 - p^-s)^-1 for Re s > 1.
- **The global functional equation:**
  - `jacobiTheta_S_smul` is the theta transformation, which is Poisson summation with the Gaussian at the real place
    and the unit balls at every p.
  - `completedRiemannZeta_one_sub` is the global functional equation Lambda(1 - s) = Lambda(s), proved through
    Hurwitz/theta kernels and the abstract Mellin functional-equation pairs of `LSeries/AbstractFuncEq.lean`.
- **Arbitrary finite test functions:** `ZMod.completedLFunction_one_sub_even` / `_odd` (`LSeries/ZMod.lean`) give the
  functional equation for the L-series of **any** even or odd Phi : Z/N -> C, relating Phi to its discrete Fourier
  transform. This is the global Poisson identity for a finite-adelic test function of level N, and it is linear in
  Phi.

---

## 2. The reductio target: an off-line pair against the local data and Poisson

Assume a pair rho, 1 - conj(rho) off the line.

**What the data give.**
- **What the data determine:** local factors, local functional equations and global Poisson together give the
  continuation, the functional equation, the poles at 0 and 1, finite order, and the Euler product for Re s > 1. By
  Hamburger's theorem (recalled), the functional equation with these gamma factors, together with the
  Dirichlet-series form, determines zeta up to a constant. So the data determine the zeros, and RH is a consequence of
  them.
- **The real question:** which consequence-route works, and what it has to use besides the duality.

**Step 1: the local data alone cannot see a zero [proved here].**
- Every local factor is zero-free: (1 - p^-s)^-1 has no zeros and has poles on Re s = 0, and Gammaℝ has no zeros.
- Tate's ratios Z_v(f_v) / L_v only add zeros.
- So the zeros of Lambda appear only in the global identity, as the zeros of the Mellin transform of the theta kernel.
  A reductio has to pass through the global Poisson identity.

**Step 2: the global identity is linear, and linear identities allow the pair [classical + Mathlib].**
- **Poisson summation is linear in the test function.** The functional equation holds for every f in the adelic
  Schwartz-Bruhat space, not only for products of local functions. Mathlib's `ZMod.completedLFunction_one_sub_odd`
  is this statement at level N, for an arbitrary odd Phi on Z/N.
- **Davenport-Heilbronn (1936, recalled):**
  - Take N = 5 and Phi = c chi + conj(c) conj(chi), with chi the character mod 5 with chi(2) = i. The constant c is
    chosen so that the Fourier transform of Phi is a multiple of Phi.
  - The resulting function satisfies a self-dual functional equation of exactly the L-function shape.
  - It has infinitely many zeros with Re s > 1, and zeros in the critical strip off the line (recalled; numerics of
    Spira, Bombieri-Ghosh).
- **So nothing in Tate's data contradicts an off-line pair:**
  - the local functional equations hold place by place;
  - global Poisson holds;
  - the real place is the same Gaussian (the odd one);
  - and the pair is there.
- `krein_off_line` (`GRH/Orbits.lean`) is the abstract version of this: the duality is preserved and the off-line
  pair 3/4, 1/4 exists. Davenport-Heilbronn is the arithmetic instance.

**Step 3: what is missing, and where it can come from [classical + proved here].** What Davenport-Heilbronn lacks is
the Euler product, i.e. the restriction to a single character, which is a pure tensor in Tate's language. The Euler
product is a **nonlinear** condition on the Dirichlet coefficients. It gives exactly one usable sign, and that sign is
local:
- **The local sign:** -L_p'/L_p(s) = (sum over k >= 1 of) log p p^(-k s) has nonnegative coefficients, so
  Lambda(n) >= 0. Each place asserts its prime powers with a positive sign. Davenport-Heilbronn's log-derivative has
  coefficients of both signs.
- **How Landau uses the sign:** Landau's theorem (a Dirichlet transform of a positive function is analytic up to a
  real singularity) needs a positive function. `INDUCTION.md` section 3 gives the full argument: from a
  **one-sided** bound psi(x) - x <= C x^(1/2 + theta), smoothed, the function C x^(1/2+theta) - (psi(x) - x) is
  positive. Its transform must then be analytic in Re s > 1/2 + theta, but an off-line zero puts a pole there. That
  is the contradiction, and the remnant is the zero-free half-plane. Lambda(n) >= 0 is what makes the transform of a
  pure prime sum behave. The repository's Lean RH proof uses this route (`landau_window`, see `GUIDE.md`).
- **The one-sided bound is not local:** it bounds a sum over all primes up to x. It does not follow from local data
  plus Poisson, since generalised-prime systems with regular integers violate it (Diamond-Montgomery-Vorhauer 2006,
  abstract). It is the "boundary part" of `INDUCTION.md` section 3: two-bump positivity, the moments of the zero
  measure.

**Where exactly the reductio needs more than the functional equation [proved here]:** at the global inequality.
- **Weil form:** positivity of all sections, which couples the places.
- **Dirichlet form:** the one-sided square-root bound, completed by the local sign Lambda(n) >= 0 and Landau.
- **The contradiction itself is cheap:** with the global inequality in hand it is a short step (Landau; or
  `atoms_on_circle` in the finite model). Without it there is no contradiction (Davenport-Heilbronn,
  `krein_off_line`).

---

## 2a. "It runs" as the formal target of the reductio

The owner's answer to "what positivity the reductio needs on top of the functional equation" was: "It runs." In the
project's language, a system runs when it has a positive evolution: an evolution that does not increase a norm, on a
space whose norm is positive.

**The evolution and its modes [classical].**
- **The flow:** scaling x -> e^t x is translation T_t f(u) = f(u - t) in u = log x. It preserves Weil's form on test
  functions exactly, by translation invariance (`INDUCTION.md` section 1a). The construction from local data gives
  this for free.
- **The modes:**
  - A zero rho = 1/2 + beta + i gamma corresponds to the mode e^((beta + i gamma) u), which T_t multiplies by
    e^((beta + i gamma) t).
  - On the line (beta = 0) the mode is a phase.
  - Off the line it grows (beta > 0), and the functional equation supplies its mirror 1 - conj(rho), which decays at
    the same rate.

**The reductio in the "runs" form [Lean template].**
- **The argument:** suppose T_t, for t >= 0, does not increase a **positive** norm on a space that contains the modes
  of all zeros. Then no mode grows. By the mirror, no mode decays either. So every mode is a phase, which is RH.
- **In Lean:**
  - `runs_and_mirror_on_line` (`Tate.lean`) is this argument for an abstract norm-nonincreasing map;
  - `atoms_inside_circle` / `atoms_on_circle` (`Induction.lean`) are the grid form;
  - `krein_off_line` (`Orbits.lean`) shows that without a positive norm a form-preserving map can have the
    eigenvalue 3/4.
- **Each ingredient does half the work:** "running forward" alone excludes only the growing half-plane. It is the
  functional equation that turns the half-plane into the line.

**Which construction, which norm [classical, recalled where marked].**

| construction | norm | positive? | sees every zero? |
|---|---|---|---|
| (A) Weil completion: test functions in u = log x, completed in Weil's form; T_t = translation | W(f * f~) | **iff RH** (the open step) | yes: the spectral measure of the flow is the zero measure |
| (B) Connes, adele class space (recalled: Selecta 1999): L^2 of the idele class group with Haar measure, and the cokernel of E f(x) = \|x\|^(1/2) (sum over q in Q^x of) f(q x) on adelic Schwartz-Bruhat functions; T_t = the scaling action | L^2 (Haar) | yes, by construction | only the zeros on the line, since a unitary flow has unitary spectrum. That there are no others is Connes's global trace formula, which is equivalent to Weil positivity |
| (C) Lax-Phillips; Faddeev-Pavlov (recalled): automorphic wave equation on the modular surface, semigroup Z(t) = P_+ U(t) P_- | energy (Laplacian >= 0) | yes | the resonances carry zeta's zeros through the scattering matrix xi(2s-1)/xi(2s). Contraction is automatic, but it confines them only to a half-plane |
| (D) one grid (`INDUCTION.md`): Toeplitz completion, Schur/Levinson recursion | Toeplitz form | **iff** every Schur parameter has \|k_N\| < 1 | yes (atoms z_rho) |

**In the grid coordinates (D), "it runs" is literal, and it holds numerically [numerical, `induction.log`].**
- **Each step is a contraction:** each Schur step is a contraction with parameter k_N, so the evolution runs at step N
  exactly when |k_N| < 1.
- **Every computed step runs, with room:** every step up to support 1.25 has |k_N| <= 0.68.
- **The norm's margin still collapses:** E_N = (product of) (1 - k_j^2) goes to about 1e-9 to 1e-11. So the system
  runs at every computed step with room per step, while the room accumulated over the whole history goes to zero.

**Where positivity of the norm would have to come from [proved here + reading].**
- **Locally it is there:**
  - Each L^2(Q_v), with Haar measure, is a positive space. The local Fourier transform is unitary, and on the line its
    Mellin multiplier is a phase (`local_factor_unimodular`).
  - The product L^2(A) is positive, and the adelic scaling action is unitary on it. But its spectrum there is
    continuous: it sees no zero.
- **The zeros appear only after the quotient by Q^x** (the Poisson step, the map E). The norm the Weil distribution
  induces on that quotient is Weil's form.
- **So positivity would have to be inherited through the quotient by the rationals,** on the functions that see the
  zeros. That inheritance is the open step, Weil positivity in Connes's language. Section 3 shows it cannot be
  arranged place by place.
- **The comparison with Yang-Mills:**
  - There, "it runs" (Osterwalder-Schrader reflection positivity, giving a transfer operator e^{-tH} with H >= 0)
    comes from a positive measure: Haar measure times e^{-S}. The action is a sum of local terms, each reflection
    positive (Osterwalder-Seiler for the Wilson action, recalled). The global object is an integral against a
    positive measure, so the positivity is built in.
  - In the arithmetic, the global object is the Weil distribution, a signed object: the primes enter with a minus
    sign, and the local prime blocks are indefinite (section 3). The positive measure on the spectral side is the
    zero measure, whose positivity is the conclusion.
  - So the Yang-Mills mechanism has no arithmetic input until a positive-measure representation of Weil's
    distribution is supplied by the construction.
- **The type of evolution also differs:**
  - **Yang-Mills:** the transfer operator is e^{-tH} with H >= 0, a real decay.
  - **Weil's flow:** it is e^{itH} with H self-adjoint, whose spectrum is the ordinates gamma, unbounded both ways. The
    reflection u -> -u (the functional equation's x -> 1/x) is present.
  - **Why OS reflection positivity is the wrong shape:** it would make the half-line pairing of D at u + v a positive
    Hankel form. By Widder's theorem (recalled), a positive Hankel form means a Laplace transform of a positive
    measure, a sum of real decays. The zeros' side is oscillatory, sum of e^{i gamma u}.
  - **So the right "runs" for RH is the unitary kind:** norm-nonincreasing forward, plus the mirror.
- **Where a positive norm came from in the one case that is solved:** for curves over finite fields, the positive norm
  is the Hodge index theorem on the surface C x C (Weil, recalled). The proposed arithmetic analogue is a Hodge index
  theorem for an "arithmetic surface" over Spec Z (Deninger; Connes-Consani's arithmetic site). That is the Deninger
  face (`ORBITS.md`).

**Answer [proved here]:**
- **Yes, the construction exists:** the adelic construction carries the scaling flow, and on the Weil completion (A)
  its being norm-nonincreasing in a positive norm is equivalent to Weil positivity.
- **The reductio then takes two lines:** an off-line pair is a growing mode, which contradicts that it runs.
- **The open part is the positivity of the norm**, which is not proving that the flow is contractive as such:
  - The construction makes the flow preserve the form for free.
  - Where the norm is positive by construction, the space either misses the off-line zeros (B) or yields a half-plane
    (C).
  - Where the space sees every zero, (A) and (D), the norm's positivity is the open step.

---

## 3. Local positivity: can Tate's freedom assemble the sign place by place?

**Weil's form splits by places [classical, recalled: Weil 1952].**
- W(g) = W_inf(g) + (sum over p of) W_p(g), for g = f * f~ on the multiplicative group, written additively in
  u = log x.
- W_p(g) = -(sum over k >= 1 of) log p p^(-k/2) (g(k log p) + g(-k log p)).
- W_inf is the real-place principal-value term together with the pole term.
- These local distributions are **canonical**: they are the logarithmic derivatives of the local factors. Tate's
  choice of f_v enters the zeta integrals, not the W_v. So "Tate's local freedom" cannot change them. The only freedom
  in a place-by-place assembly is to move a piece of one local term into another, keeping the sum fixed.

**What can be moved [Lean + proved here].**
- **The lattices are disjoint:** the lags k log p of different primes never meet for k >= 1
  (`prime_lattices_disjoint`, unique factorisation). They also never meet the absolutely continuous real-place term.
  So a redistribution c_v with (sum of) c_v = 0, each c_v living where its place lives, can only be a multiple of
  delta_0. On a grid section that is a multiple of the identity matrix.
- **Each prime block is indefinite:** each P_p (the block of the prime p on a grid section) has zero diagonal,
  because log p > (cell support), and it is symmetric. So it is indefinite as soon as it is non-zero
  (`zero_diag_indefinite`).
- **Hence the real place would have to be positive on its own:** the shifts with P_p + a_p I >= 0 have a_p >= 0, so
  the real place gets a_inf = -(sum of) a_p <= 0, and its own form must be positive
  (`local_assembly_forces_arch`).
- **The exact condition:** place-by-place positivity holds exactly when lambda_min(A) >= (sum over p of) c_p, where
  c_p = -lambda_min(P_p) >= 0.

**The numbers [numerical]** (`tate.log`, all relative to t_0; grid r = 3, eps = 0.05):

| support a | lambda_min(A) (real place + pole) | sum of c_p (primes present) | slack = lambda_min(A) - sum c_p | lambda_min(whole form) |
|---|---|---|---|---|
| 0.325 | 0.014 | 0 (no prime yet) | +0.014 | 0.014 |
| 0.350 | 0.0052 | 3.6e-7 (2 enters) | +0.0052 | 0.0052 |
| 0.400 | 0.0016 | 0.25 | -0.25 | 8.6e-4 |
| 0.425 | -0.12 | 0.59 | -0.71 | 2.9e-4 |
| 0.575 | -0.74 | 0.88 (2, 3) | -1.6 | 1.3e-7 |
| 0.875 | -1.8 | 3.4 (2, 3, 5) | -5.2 | 7.3e-9 |
| 1.225 | -3.2 | 6.6 (2 to 11) | -9.7 | 9.9e-10 |

The r = 1 grid gives the same picture: the slack turns negative at 0.35 and reaches -3.8 by 1.225, while the whole
form stays at +8e-4.
- **Place-by-place positivity holds only until the prime 2 enters.** That is consistent with an archimedean positivity
  window ending near (1/2) log 2 (Connes-Consani, abstract).
- **After that, every place is far from positive on its own,** and the whole form is positive only by cancellation
  between the places, to 1e-9 out of terms of order 1 to 10.
- **Semilocal truncations fail too:** keeping every place below p* and dropping p* breaks positivity within 0.014 to
  0.05 of (1/2) log p* (`induction.log` part 2). So the positivity needs **every** place up to e^(2a), together.

**Ramified places are the one exception, and it does not help [classical, recalled].**
- For a character ramified at p, L_p = 1. The p-term of the explicit formula reduces to the conductor term
  (log of the conductor) g(0) >= 0, which is positive.
- So Tate's freedom can make a local term positive only by passing to a ramified character. That removes the Euler
  factor and changes the L-function. It does not touch the positivity problem for zeta.

**Answer to item 3 [proved here + numerical]:** no. Tate's local freedom does not act on Weil's local distributions.
The only redistribution that respects locality is the lag-0 part. With zero-diagonal prime blocks, place-by-place
positivity would force the real place to be positive and to dominate the sum of the primes' negative parts. That fails
from support about 0.4 on, by an amount that grows to 9.7 t_0 at support 1.225.

---

## 4. Lean

`ProofPhase/GRH/Tate.lean` builds clean, with no warnings in the file. `axioms-tate.log` shows propext,
Classical.choice and Quot.sound only:
- `local_factor_unimodular`: for x > 0 and s = 1/2 + i t, |1 - x^(-s)| = |1 - x^(s-1)|. So Tate's unramified gamma
  factor is a phase on the line.
- `prime_lattices_disjoint`: k log p != l log q for distinct primes and k >= 1.
- `form_two_point`, `zero_diag_indefinite`: a real symmetric form with zero diagonal and a non-zero entry takes a
  negative value (on e_i - A_ij e_j).
- `local_assembly_forces_arch`: if the places exchange only multiples of the identity, every prime block has zero
  diagonal, and every shifted local form is nonnegative, then each prime's share is nonnegative and the real place's
  own form is nonnegative.
- `runs_and_mirror_on_line`: a map that does not increase a positive norm, with an eigenvalue mu != 0 and the mirror
  eigenvalue (conj mu)^-1, has |mu| = 1. This is the "it runs + functional equation" reductio in abstract form;
  compare `krein_off_line`, the same situation without a positive norm.

**Not formalised:**
- Davenport-Heilbronn as an instance of `ZMod.completedLFunction_one_sub_odd`. It needs the discrete Fourier
  transform on Z/5 with values in Q(sqrt 5, i): bookkeeping, nothing deep.
- The adelic Poisson formula itself, which Mathlib reaches through theta rather than adelically.

---

## 5. Numerics summary

| what | result | file |
|---|---|---|
| zero diagonal of every prime block | exact 0 for p = 2 to 13 | `tate.log` |
| place-by-place condition | holds up to a = 0.35 and fails from a = 0.40 on (r = 3; from 0.35 for r = 1); slack -9.7 t_0 at a = 1.225 (r = 3) | `tate.log` |
| whole form | positive at every support, 9.9e-10 t_0 at a = 1.225 | `tate.log` |
| semilocal truncations | fail within 0.014 to 0.05 of (1/2) log p* | `induction.log` part 2 |

---

## 6. Where it stops, and the relation to the six earlier faces

**The stop:**
- **The first unclosable step:** a global inequality that couples every place up to the scale. In Weil's form it is
  positivity of the section. In the "runs" form (section 2a) it is the positivity of the norm in which the scaling
  flow runs, i.e. positivity inherited through the quotient by the rationals. In Dirichlet form it is the one-sided
  square-root bound for psi(x) - x, which the local sign Lambda(n) >= 0 and Landau then turn into the contradiction.
  **[open]**
- **What does not supply it:**
  - the local functional equations and global Poisson (Davenport-Heilbronn; `krein_off_line`);
  - Tate's local freedom (it moves no zero and does not touch W_v);
  - place-by-place positivity (impossible: Lean + numbers).

**The six earlier faces, seen from Tate's frame:**
1. **Weil Hilbert space (ATTEMPT step 4):** its inner product is the global form. Tate's frame shows it cannot be a
   product or sum of local positive inner products, because the local pieces are indefinite.
2. **Critical ferromagnet (LEE-YANG):** Lee-Yang/Asano is a local assembly that works, because the couplings are
   ferromagnetic (positive). Here the local couplings, the prime blocks, are provably indefinite (zero diagonal). That
   is the precise sense in which the primes are "not a ferromagnet".
3. **Deninger space (ORBITS):** a positive Hodge form is global (cohomological), which is consistent with the finding
   that the sign cannot be local. Deninger's local orbits (the primes) would be indefinite contributions to a positive
   whole, as here.
4. **Hermite-Biehler chain (INDUCTION section 5):** the local factors are phases on the line (Lean), so each place is
   "unitary". The Hermite-Biehler property of xi is the global statement about the product of these phases with the
   theta integral.
5. **Step lemma (INDUCTION section 7):** the margin at each scale is the residue of a cancellation among all places
   (local slack -9.7 against global +1e-9). The step lemma has to be proved for the global sum, not place by place.
6. **Sign of the remnant (VARIATIONAL):** the same quantity, lambda_min of the whole section. Tate's frame adds that
   no place carries it.

**De Bruijn-Newman [classical, recalled]:**
- **The deformation:** in Tate's coordinates, the heat-flow deformation H_t of the theta kernel (de Bruijn; Newman)
  deforms the real place's datum.
- **The edge:** RH is the statement that the de Bruijn-Newman constant is at most 0. Rodgers and Tao proved it is at
  least 0, so every backward deformation produces off-line zeros.
- **So the sign holds exactly at the edge.** This is the global, continuum version of the 1e-9 margins
  (`INDUCTION.md`, `VARIATIONAL.md`).

---

## 7. DMP reading (separate; not mathematics)

This section reads the owner's words against the mathematics above. Nothing here is a claim of the note.

- **"The functional equation proven to be locally evaluable":** this matches Tate exactly. Each place has its own
  functional equation, and its factor is a pure phase on the critical line (Lean for the primes). So "running"
  in the owner's sense has a precise counterpart: at every place the local evolution (the local Fourier transform)
  is unitary on the line. The link to G0, read as the critical line, is evaluable place by place.
- **"From which the causality of existence is derived":** the local phases combine only in the global Poisson
  identity. That is also the only place where zeros are created (every local factor is zero-free). In the owner's
  terms: existence (the zeros, the spectrum) is a property of the whole closed system, not of any place. That fits
  the earlier reading that the circle is the only self-closed existence.
- **The reductio ("excised at once"):** the local functional equations cannot excise an off-line pair. The pair
  disagrees with nothing local: Davenport-Heilbronn carries such pairs with every local equation intact. The excision
  needs a disagreement with a sign.
  - **The local sign:** the one local sign there is, Lambda(n) >= 0, can be read as "each act asserts with a positive
    sign". It is the remnant of the Euler product, and it is what Davenport-Heilbronn lacks.
  - **The global bound:** the bound that the sign is excised against is global: no alignment of the prime phases may
    overtake the growing mean. That is the earlier "virtual flux" reading, now in its exact place.
- **"The thing on top the reductio needs: It runs":** this is the right formal target (section 2a).
  - "Running" is an evolution that does not increase a positive norm. With the mirror from the functional equation,
    it puts every mode on the line (Lean, abstract). An off-line pair is a growing mode, so a running system
    excises it at once: that is the earlier "disagreement at G0".
  - **What the construction gives:** the evolution itself, which preserves the form automatically.
  - **What it does not give:** the positivity of the norm. Locally the norm is positive. In the owner's terms, what
    must be shown is that the running survives the closure, the quotient by the rationals, where existence (the
    zeros) is created.
  - **The numbers support "it runs":** on one grid every step contracts with room (|k| <= 0.68). But the room
    accumulated over the history shrinks to about 1e-9.
- **Verdict:** the approach is the right frame for the mirror. Locality, unitarity on the line, and "running" are all
  exact and all local. But it shows sharply that the sign is not local. The best approach therefore needs one global
  inequality on top of the locally evaluable functional equation, and that inequality is the same open step as in the
  six earlier faces.

---

## 8. Files and references

**Files:**
- `tate.py`, `tate.log`: place-by-place assembly against the whole form (13 s, mpmath 60 digits; reuses
  `induction.py`'s grid).
- `docs/mass-gap/formal/ProofPhase/GRH/Tate.lean`, `axioms-tate.sh`, `axioms-tate.log`.

**Mathlib anchors** (repository's pinned version):
- `Gammaℝ`;
- `riemannZeta_eulerProduct_tprod`;
- `jacobiTheta_S_smul`;
- `completedRiemannZeta_one_sub`;
- `ZMod.completedLFunction_one_sub_even`, `ZMod.completedLFunction_one_sub_odd`;
- `LSeries/AbstractFuncEq.lean` (WeakFEPair).

**References:**
- Recalled:
  - J. Tate, thesis (1950); A. Weil, explicit formulas (1952); H. Hamburger (1921);
  - H. Davenport, H. Heilbronn (1936); R. Spira; E. Bombieri, A. Ghosh, on the Davenport-Heilbronn function;
  - A. Connes, trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Selecta Math. (1999);
  - P. Lax, R. Phillips, scattering theory for automorphic functions (1976); L. Faddeev, B. Pavlov (1972);
  - K. Osterwalder, R. Schrader; K. Osterwalder, E. Seiler (reflection positivity of the Wilson action); D. Widder;
  - A. Weil, curves over finite fields (1948), Hodge index on C x C;
  - B. Rodgers, T. Tao, the de Bruijn-Newman constant is non-negative (2020); N. G. de Bruijn; C. M. Newman.
- H. Diamond, H. Montgomery, U. Vorhauer, Math. Ann. 334 (2006). Abstract-level.
- A. Connes, C. Consani, arXiv:2006.13771. Abstract read.
