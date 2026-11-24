# The closed-orbit route: primes as the remnants of a flow

Private working note, 2026-11-23. Follows `ATTEMPT.md`, `SEMILOCAL.md` and `LEE-YANG.md`. The owner's reading
(PREP.md, "GRH is missing the concept of the remnant of acts"): "the remnants become the evidence of causality, by
which the system proves it runs". The mathematical counterpart: over a finite field, zeta counts the fixed points of
Frobenius (Lefschetz). Deninger proposes that the primes are the closed orbits of a missing flow, of lengths log p,
with the explicit formula as its trace formula.

As in LEE-YANG.md, section 0: RH and Dirichlet GRH are theorems (the Lean library). "Open" below means an independent
proof along this route, not the truth of the statements.

**Claim marks** as in `ATTEMPT.md`, plus **[Lean-orb]** = proved in `docs/mass-gap/formal/ProofPhase/GRH/Orbits.lean`
(standard axioms only; `axioms-orbits.sh`, `axioms-orbits.log`). Items recalled from the literature rather than
re-read in this session say so.

---

## 0. The verdict in plain words

- **The remnant picture is fully present over the integers.** The closed orbits (primes, lengths log p) and their
  repetitions (prime powers), the stationary part (the real place), and the trace formula (the explicit formula, which
  we checked to 1e-16) are all there. What Deninger's programme lacks is the space that carries the flow, not its
  shadows **[classical]** (recalled) + **[numerical]** (ATTEMPT.md section 4).
- **The remnants do not give a new positivity.** Remnant counts are non-negative, as counts must be, but that is the
  weight positivity of the Euler product. This note series has now shown three times that it is insufficient
  (SEMILOCAL: each orbit's contribution has mean zero; LEE-YANG step 3: positive weights with off-line zeros; BRIDGE:
  positivity is one-sided). Over a finite field, too, RH comes from a positivity *on cohomology* (Rosati / Hodge
  index), not from the counts **[classical]**.
- **In finite form, in Lean:** remnants are counted by closed orbits (`card_fixed_pow_eq_sum`); a positive form on
  which the dynamics acts by similitude forces the line (`similitude_eigenvalue`, `skew_shift_re_half`); a duality
  *without* positivity forces only mirror pairs, with an explicit off-line example (`krein_off_line`). So the trace
  formula and the duality give the mirror; only the positive form gives the line **[Lean-orb]**.
- **The step that cannot be closed:** construct Deninger's space, a foliated space with a flow whose closed orbits
  are the primes, whose stationary part is the real place, and whose leafwise cohomology H^1 carries a positive Hodge
  form for which the flow acts by similitudes with factor e^t. The positivity must come from the geometry of that
  space, as it does from the surface C x C over a finite field. No such space is known **[open]**.
- **Relation to the earlier blocking steps: the same obstacle again, in its geometric dress.** Deninger's H^1 with its
  Hodge form is, once positivity is known, the Hilbert space that Weil's form builds (ATTEMPT.md step 4), with the
  flow as its translation group. In the Lee-Yang dictionary, "Theta - 1/2 is skew" is "the single spin Phi has the
  Lee-Yang property". All three steps ask for the same positivity. Each names a different place it might come from:
  a Hilbert-space structure (step 4), a critical ferromagnet (LEE-YANG step 5c), or a foliated geometry with Hodge
  theory (here). Step 4 is the weakest structure; the other two would each imply it.

---

## 1. Step a: Deninger's dictionary, precisely

The dictionary is from Deninger (ICM 1998; Jahresbericht DMV 2001; later surveys, recalled), together with Leichtnam's
survey (2005). It is set beside a curve C over F_q and beside the objects of this note series.

| Curve C over F_q (Weil, Grothendieck) | Spec Z, completed (Deninger, conjectural) | Our objects |
|---|---|---|
| Frobenius F, discrete time n | a flow phi^t on a 3-dimensional foliated space X, t real, mapping leaves to leaves | the log-scale variable u of Weil's form; the spin variable u of LEE-YANG |
| fixed points of F^n: the points of C over F_{q^n} | closed orbits gamma_p of length l = log p, and their k-fold repetitions | the prime-power terms h(+-k log p) |
| Lefschetz: #C(F_{q^n}) = sum over i of (-1)^i Tr(F^n on H^i) | a transversal (Guillemin-Sternberg) trace formula for the flow on leafwise cohomology H^i_F | the explicit formula, checked to 1e-16 |
| H^0, H^2: Frobenius eigenvalues 1 and q | H^0_F, H^2_F: generator Theta of the flow with eigenvalues 0 and 1 | the pole terms at s = 0, 1 (F(+-i/2)) |
| H^1: eigenvalues alpha_i | H^1_F: spectrum of Theta = the zeros rho | the zero side sum of \|F(gamma)\|^2 |
| Poincare duality: alpha <-> q / alpha | duality: rho <-> 1 - conj(rho) | the functional equation; spin flip |
| Rosati / Hodge-index positivity gives \|alpha\| = sqrt(q) (Weil) | a leafwise Hodge form with Theta - 1/2 skew-adjoint gives Re rho = 1/2 (conjectural) | Weil positivity; the Lee-Yang property of Phi |
| (no counterpart) | stationary points of the flow: the real place | the archimedean term, symbol log(r / 2pi) (SEMILOCAL 3a) |

**The trace formula.** For a flow with non-degenerate closed orbits gamma and stationary points x, the
Guillemin-Sternberg distributional trace formula reads schematically

  "sum over i of (-1)^i Tr( int f(t) phi^{t*} dt on H^i_F )" = sum over gamma of l(gamma) sum over k >= 1 of
  eps_gamma(k) f(k l(gamma)) + (contributions of the stationary points) + (the same for t < 0).

With l(gamma_p) = log p and after the twist by the half-density e^{t/2}, the first sum is the prime side of the
explicit formula. The stationary points give its archimedean term **[classical]** (Guillemin 1977;
Guillemin-Sternberg 1977; Deninger's matching, recalled).

**What is proved about it** (recalled, not re-read):
- **Trace formulas for foliated flows** in geometric settings: Alvarez Lopez and Kordyukov for Riemannian foliations
  and Lie foliations, in distributional form.
- **Hodge theory on foliations.** Deninger and Singhof showed that leafwise cohomology of Riemannian foliations with
  suitable flows carries real polarizable Hodge structures, a positivity of the kind needed, in their geometric
  examples. They also gave a counterexample to a smooth leafwise Hodge decomposition for general foliations, so the
  geometry has to be special.
- **Candidates for the space.** Connes's adele class space A_Q / Q^*, with the scaling action of R_+^*: its trace
  formula is the explicit formula, the zeros appear as an absorption spectrum, and its positivity is equivalent to RH
  (Connes 1999). Connes and Consani's arithmetic and scaling sites (2014-2018) are geometric objects with a
  Frobenius-like action.
- **Arithmetic topology.** Primes as knots in a 3-dimensional Spec Z (Mazur, Morishita, "Knots and Primes") and Kim's
  arithmetic Chern-Simons theory: the same "primes as closed loops" picture, without a flow that produces RH.

None of these gives an X over Spec Z with the positive Hodge form **[open]**.

---

## 2. Step b: connecting it to what we have

- **Each prime is one closed orbit, and its "wobble" is that orbit's contribution.** In SEMILOCAL.md 3a each prime
  contributes the frequency weight phi_p(r) = 2 Re (L_p'/L_p)(1/2 + ir): periodic, with period 2 pi / log p, and mean
  zero. In trace-formula terms its Fourier series lives at the frequencies k log p, the length spectrum of the orbit
  gamma_p and its repetitions. A test function supported in [-a, a] sees exactly the orbits of length <= 2a. The
  semilocal finding (positivity needs every prime up to e^{2a}) reads: **the spectral side is positive only if every
  closed orbit the test function can see is included.** No orbit is optional **[numerical]** + **[reading]**.
- **The real place is the flow's continuous part.** Its weight phi_inf(r) ~ log(r / 2pi) is the average density of
  the spectrum (Riemann-von Mangoldt). In Deninger's picture it is the stationary-point contribution: smooth,
  positive in the mean, no orbit structure **[classical]**.
- **The Lee-Yang single spin is the flow time.** In xi(1/2 + h) = int Phi(u) e^{hu} du (LEE-YANG section 3) the spin
  variable u is the log-scale coordinate, i.e. Deninger's flow time t, and the field h = s - 1/2 is the eigenvalue of
  Theta - 1/2. Through xi = "det(s - Theta on H^1)" (regularised, conjectural), "the single spin Phi has the Lee-Yang
  property" is "Theta - 1/2 has purely imaginary spectrum". Phi itself comes from the theta function, i.e. from the
  real place, the stationary part **[reading]** on **[classical]** inputs.
- **In finite form** (`card_fixed_pow_eq_sum`) **[Lean-orb]**: for any map on a finite set, #Fix(f^n) equals the sum
  over d dividing n of #{points of exact period d}. Each closed orbit of length d contributes d points at every
  multiple of d. This is the finite skeleton of the prime side: lengths l(gamma) at multiples k l(gamma).

---

## 3. Step c: do the remnants give a positivity that weight positivity lacks?

**No.** The positivity the remnants carry is the positivity of counts. Over a finite field N_n >= 0; over Z the
weights Lambda(n) >= 0, i.e. the Euler product. This is the Euclidean, Hankel-type positivity that Landau's theorem
uses (BRIDGE, Part 1). It is provably insufficient:
- SEMILOCAL.md: each orbit's contribution on the frequency axis has mean zero and is indefinite.
- LEE-YANG.md step 3: positive weights e^{tu^2} Phi with off-line zeros for every t < 0.
- Over F_q itself: N_n >= 0 together with Stepanov's one-sided bound gives only the upper half; Weil's proof of RH
  for curves uses a positivity on cohomology (Castelnuovo, Hodge index, Rosati) **[classical]** (BRIDGE.md 2.2-2.3).

**What does give the line, in finite form** **[Lean-orb]**:
- `similitude_eigenvalue`: if <F x, F y> = q <x, y> for a positive-definite inner product, every eigenvalue alpha of
  F has \|alpha\|^2 = q. This is the curve case (Rosati positivity plus F V = q).
- `skew_shift_re_half`: if <Theta x, y> + <x, Theta y> = <x, y> for a positive-definite inner product (Theta - 1/2
  skew-adjoint: the flow acts by similitudes with factor e^t), every eigenvalue rho of Theta has Re rho = 1/2. This is
  Deninger's mechanism, in finite dimension.
- `krein_mirror`, `krein_off_line`: on C^2 with the *indefinite* Hermitian form B(x, y) = conj(x_0) y_1 +
  conj(x_1) y_0 (a duality pairing, `kreinForm_indefinite`), the operator Theta = diag(rho, 1 - conj(rho)) satisfies
  the same identity B(Theta x, y) + B(x, Theta y) = B(x, y) for **every** rho. Its eigenvalues are the mirror pair
  rho, 1 - conj(rho); for rho = 3/4 they are 3/4 and 1/4, off the line. **A duality with the right similitude law and
  the right trace structure gives only the functional equation's mirror pairs. Positivity of the form is what puts
  them on the line.**

**The missing statement, exactly:**

> There is a complex Hilbert space H (Deninger's H^1_F) with a positive-definite inner product, and a generator Theta
> with Theta - 1/2 skew-adjoint (equivalently, the flow e^{t Theta} acts by similitudes with factor e^t). Its trace
> formula, Tr( int f(t) e^{t Theta} dt on H ) in the regularised sense, equals the arithmetic side of Weil's form:
> the closed orbits (primes) plus the stationary part (real place) plus the pole terms (H^0, H^2). And H is
> constructed from the geometry of a space X, not from the zeros.

Given H, `skew_shift_re_half`, in its spectral-theorem version for unbounded operators, gives RH.

**Why it is the same obstacle as step 4** **[proved here]**, on classical inputs. If Weil's form W is positive (which
is now known, as a consequence of GRH), the GNS completion of the test functions under W is a Hilbert space on which
translation in u acts unitarily, by translation invariance of W. With the twist by e^{t/2}, translation becomes a
similitude with factor e^t, i.e. Theta - 1/2 skew. Its trace formula is the explicit formula by construction.
Conversely, H as above makes W positive. So "H exists" is ATTEMPT.md step 4 plus the trace-formula identification.
What Deninger adds is a proposal for *where the positivity comes from*: the Hodge theory of a geometric space, as the
Hodge index theorem on C x C supplies it over F_q.

---

## 4. Step d: the paper argument, step by step

1. **Remnants and trace formula.** Primes as closed orbits of length log p, prime powers as repetitions, the real
   place as stationary part, the explicit formula as trace formula. The formal matching is classical (recalled), and
   the explicit formula was checked numerically. **[classical]** + **[numerical]**
2. **Remnant positivity.** Counts and weights are non-negative. **[classical]**, trivially.
3. **Remnant positivity is insufficient.** It is the weight positivity already shown insufficient (section 3).
   **[proved here]** + **[numerical]** + **[classical]**
4. **Duality gives the mirror only.** A duality pairing with the similitude law permits every mirror pair (rho,
   1 - conj rho) unless it is positive definite. **[Lean-orb]** (`krein_off_line`)
5. **Positivity on cohomology gives the line.** **[Lean-orb]** in finite dimension (`skew_shift_re_half`,
   `similitude_eigenvalue`); the infinite-dimensional version is the spectral theorem **[classical]**.
6. **Construct the space X whose leafwise cohomology carries the positive Hodge form.** Not known: no candidate (the
   adele class space, the arithmetic or scaling site, arithmetic topology) has been shown to carry a positive Hodge
   form with the explicit formula as trace formula. **[open]** **The route stops here.**

**The blocking step, named precisely:**

> **Step 6.** A foliated space X with a flow phi^t such that: its closed orbits are the primes, with lengths log p;
> its stationary part produces the archimedean term; its leafwise cohomology H^1_F has a Hodge inner product,
> positive by the geometry of X, for which phi^t acts by similitudes with factor e^t; and its transversal trace
> formula is the explicit formula. Given X, step 5 gives RH (and, for twisted versions, GRH for Dirichlet characters)
> by a positivity mechanism. Over F_q the corresponding object is the curve itself, and the positivity is the Hodge
> index theorem on C x C.

**Relation to the other blocking steps.** The same obstacle in a third dress:
- **ATTEMPT.md step 4** asks for the positive Hilbert-space structure as such. Deninger's H^1 is that structure with
  the flow as its translation group (section 3).
- **LEE-YANG.md step 5c** asks for a critical ferromagnet whose block spin is Phi. Under the dictionary of section 2
  (spin value = flow time, field = eigenvalue of Theta - 1/2), its conclusion, the Lee-Yang property, is the
  conclusion here, "Theta - 1/2 skew".
- **Order by strength of what must be built:** step 4 (a positive form) is implied by either of the others (a
  geometric space with Hodge theory; a ferromagnetic lattice system). None of the three is weaker than step 4.

**Numerics.** None were run. The obstacle is structural, and the explicit-formula side was already checked in
ATTEMPT.md.

---

## 5. DMP reading (separate; not mathematics)

> **The owner's reading (PREP.md): "What GRH is missing is its concept of the remnant of acts ... once run as content
> in DMP, the remnants become the evidence of causality, by which the system proves it runs, this also certifies
> everything running as inherently existing." Nothing here is a mathematical result.**

- **"The remnants of acts":** *exact correspondence.* Over a finite field the remnants are the fixed points of the
  iterates of Frobenius, and Lefschetz turns their count into a trace of the dynamics; over Z they are the primes as
  closed orbits, counted by the explicit formula. In finite form: `card_fixed_pow_eq_sum` (the remnants of n steps are
  the closed orbits whose length divides n).
- **"Evidence of causality, by which the system proves it runs":** *supported as a description.* The explicit formula
  *is* a trace formula of Lefschetz type. The remnants are present and their count has exactly the shape a running
  dynamics would produce. In that sense the arithmetic side shows the traces of a run, even though the space that
  runs is unknown.
- **"Certifies everything running as inherently existing":** *does not fit as a proof step.* The remnants certify the
  trace formula and their counts are positive (existence of the remnants). But positivity of counts is weight
  positivity, and it does not certify the line. The Krein example (`krein_off_line`) is a dynamics with a duality and
  a trace formula of the same shape whose eigenvalues are off the line. What certifies the line is a positivity on the
  cohomology, a property of the space that runs, not of its remnants.
- **Verdict:** **supports** the reading that the primes are the remnants (closed orbits) of a dynamics and that their
  count is the evidence of a run, which is the precise content of Deninger's dictionary. **Does not support** the step
  from "the remnants exist" to "the zeros are on the line": that needs the running space's own positive form, the
  missing step 6. In the owner's earlier words, the remnants show the system *would* run; the space that runs, with
  its positivity, is still to be built.

---

## 6. Files and references

**Files.** `docs/mass-gap/formal/ProofPhase/GRH/Orbits.lean` (7 theorems, standard axioms, 0 warnings);
`docs/rh-guide/grh/axioms-orbits.sh`, `.log`.

**References** (recalled unless noted).
- C. Deninger, "Some analogies between number theory and dynamical systems on foliated spaces", Doc. Math. Extra
  Vol. ICM 1998, I, 163-186; "Number theory and dynamical systems on foliated spaces", Jahresber. DMV 103 (2001);
  E. Leichtnam, "An invitation to Deninger's work on arithmetic zeta functions" (2005).
- C. Deninger, W. Singhof, "A counterexample to smooth leafwise Hodge decomposition for general foliations and to a
  type of dynamical trace formulas", Ann. Inst. Fourier 51 (2001); "Real polarizable Hodge structures arising from
  foliations", Ann. Global Anal. Geom. 21 (2002).
- V. Guillemin, "Lectures on spectral theory of elliptic operators", Duke Math. J. 44 (1977); V. Guillemin,
  S. Sternberg, *Geometric Asymptotics* (1977); J. A. Alvarez Lopez, Y. A. Kordyukov, papers on distributional
  trace formulas for foliated flows (2000s).
- A. Connes, "Trace formula in noncommutative geometry and the zeros of the Riemann zeta function", Selecta Math. 5
  (1999); A. Connes, C. Consani, "The arithmetic site" (2014) and "Geometry of the scaling site" (2017).
- M. Morishita, *Knots and Primes* (2012); M. Kim, "Arithmetic Chern-Simons theory I" (2015).
- A. Weil, *Varietes abeliennes et courbes algebriques* (1948) (Rosati positivity); A. Grothendieck, SGA 4 1/2
  (Lefschetz trace formula); R. Hartshorne, *Algebraic Geometry*, V.1 (Hodge index; the Riemann hypothesis for curves
  via Castelnuovo-Severi).
