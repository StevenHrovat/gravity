# The Lee-Yang / Newman route: how far toward a positivity proof

Private working note, 2026-11-23. Follows `ATTEMPT.md` and `SEMILOCAL.md`. The owner's readings since the attempt
(PREP.md, last entries) are: the real place carries existence; the primes are free U(1) phases (Kronecker, Voronin);
the arithmetic side "exists but never runs" (there is no Frobenius); and "the dynamics that make it run is that it
can be run as content in a DMP-complete system". The candidate route is to find a ferromagnetic, reflection-positive
system whose partition function is xi, or whose Euclidean-time evolution is the de Bruijn-Newman flow.

**Claim marks** as in `ATTEMPT.md`, plus **[Lean-ly]** = proved in `docs/mass-gap/formal/ProofPhase/GRH/LeeYang.lean`
(standard axioms only; `axioms-leeyang.sh`, `axioms-leeyang.log`). Items recalled from the literature rather than
re-read in this session say so.

---

## 0. First, a correction of framing (it affects ATTEMPT.md step 4)

RH and GRH for Dirichlet L-functions are **theorems**: the Lean library released on 2026-11-20 proves them (guide,
section 1; S1, S2) **[Lean]**. So every statement in these notes that is "equivalent to GRH" is now *true*:
- Weil positivity holds for every Dirichlet character, because GRH implies it via the explicit formula **[classical]**.
- The de Bruijn-Newman constant is exactly Lambda = 0: Rodgers and Tao proved Lambda >= 0, and RH gives Lambda <= 0
  **[classical]** + **[Lean]**.
- In ATTEMPT.md step 4, the Hilbert-space map Phi does exist. Completing the test functions under the arithmetic
  side of Weil's form (primes, characters and the real place; no zeros used) is a legitimate construction, because
  positivity is now known.

What remains open is not the truth of these statements but **an independent proof along the positivity route**: one
that gets the positivity from the positive structure itself, not from GRH. "Open" in ATTEMPT.md step 4, and below,
means that. ATTEMPT.md is committed and stays as it is; this paragraph is the correction.

---

## 1. Where it stops (the verdict in plain words)

- **The dictionary is exact.** xi(s) is the partition function of a *single continuous spin* u, with weight Phi(u)
  (Riemann's Phi function, which comes from the theta function, i.e. the real place), in the magnetic field
  h = s - 1/2. The critical line is the imaginary-field axis; the functional equation is spin-flip symmetry. RH is
  the Lee-Yang property of that one spin **[proved here]**, on classical facts.
- **Positivity of the weight is not enough, and xi sits exactly at the edge.** The weights e^{tu^2} Phi(u) are positive
  for every t. But for every t < 0 their transforms have non-real zeros (Rodgers-Tao), while at t = 0 all zeros are
  real (RH, now proved). So any proof must use a property beyond positivity, one that holds at t = 0 and fails for
  every t < 0. The Lee-Yang (ferromagnetic) property is such a property **[classical]** + **[proved here]** for the
  logical consequence.
- **The Lee-Yang mechanism cannot run on the Euler product.** Lee-Yang moves *local zeros* onto the circle by
  contraction. Every local factor of the completed zeta function, the Gamma factor and each (1 - p^{-s})^{-1}, has no
  zeros at all. The zeros of xi are not inherited from anything local **[proved here]**. This fits the semilocal
  test: positivity needs every prime up to the scale at once.
- **The primon gas / Bost-Connes system runs zeta, but on the wrong side.** Its partition function is zeta(beta) for
  real beta > 1. The zeros sit at complex beta = 1/2 + i gamma, beyond the phase transition at beta = 1, where the
  system has no partition function and positivity says nothing **[classical]**.
- **The step that cannot be closed:** construct a ferromagnetic lattice system, with Lee-Yang single-site measures and
  non-negative couplings, whose block-spin law is Phi(u) du. Because Lambda = 0, it would have to be a ferromagnet at
  its critical coupling. Newman's closure theorems would then give RH by a positivity mechanism. No such system is
  known **[open]**.
- **Relation to ATTEMPT.md step 4: the same obstacle in a different and stronger form, not a weaker one.** A Lee-Yang
  representation would imply RH, hence Weil positivity, hence step 4. It also says *which* positivity is missing: a
  positivity of couplings (ferromagnetism) at criticality, not of weights. Weight positivity (Euclidean, Hankel) is
  available and provably insufficient. In ATTEMPT.md the margin collapsed super-exponentially; here it is exactly
  zero (Lambda = 0).

---

## 2. Step a: the three constructions, what each gives and what it lacks

| Construction | What it gives | What it lacks |
|---|---|---|
| **Primon gas** (Julia; Spector) and **Bost-Connes system** (1995) | zeta(beta) = Tr e^{-beta H} for a free gas with one-particle energies log p; Bost-Connes: a C*-dynamical system (Hecke algebra) with time evolution, KMS states, a phase transition at beta = 1 with spontaneous breaking of the symmetry group (the Galois group of the maximal abelian extension of Q) **[classical]** | The zeros are Fisher zeros in complex *temperature* beta = 1/2 + i gamma, inside beta < 1, where the trace diverges. The gas is free: Z is a product of one-prime factors with no zeros, so nothing forces zeros anywhere. KMS positivity holds at real beta > 1 only. |
| **Lee-Yang circle theorem** (1952), **Asano contraction** (1970) | Zeros of a ferromagnet's partition function in the *field* variable lie on the unit circle; from local positivity (each bond's factor is zero-free on the open bidisc) plus gluing by contraction plus spin-flip symmetry **[classical]**; smallest cases in Lean **[Lean-ly]** | A local factorisation with local zeros. zeta's local factors have none (section 3). Newman's reformulation (below) moves the question to one spin with weight Phi, whose Lee-Yang property is the whole question. |
| **De Bruijn-Newman flow** | H_t(z) = int_0^inf e^{t u^2} Phi(u) cos(z u) du solves the backward heat equation dH/dt = -d^2H/dz^2. Real zeros stay real for later t (de Bruijn 1950); all zeros are real for t >= 1/2 (de Bruijn); Lambda <= 0.22 (Polymath 2019); Lambda >= 0 (Rodgers-Tao 2020). With RH now proved, Lambda = 0 **[classical]** + **[Lean]** | A starting mechanism: the flow improves real-rootedness only forward in t. RH is the statement at t = 0, exactly the threshold, with no slack in either direction. |

**Newman's link** (Newman 1976, "Fourier transforms with only real zeros"; recalled). A probability measure rho on the
line has the **Lee-Yang property** if its moment generating function int e^{hu} drho(u) vanishes only at purely
imaginary h. This class:
- contains the Ising spin (+-1), the uniform measure on [-1, 1], and the quartic measures e^{-a u^4 - b u^2} du
  (a > 0, b real; Griffiths-Simon);
- is closed under products and weak limits;
- keeps the property when the measure is multiplied by e^{t u^2} with t >= 0 (de Bruijn's theorem in this language);
- is closed under ferromagnetic coupling: if each spin of a ferromagnet has a Lee-Yang a priori measure, then so does
  the law of the total magnetisation.

RH is equivalent to: Phi(u) du is a Lee-Yang measure. Newman also conjectured Lambda >= 0, "RH, if true, is only
barely true", which Rodgers and Tao proved.

---

## 3. Step b: the target, and whether Asano can run on the Euler product

**The exact dictionary** **[proved here]** on classical inputs (Riemann's integral for xi):
- Xi(z) = xi(1/2 + iz) = int Phi(u) e^{izu} du, with Phi even and positive (Polya; recalled).
- Put h = s - 1/2, so z = -ih. Then xi(1/2 + h) = Xi(-ih) = int Phi(u) e^{hu} du: **the partition function of one
  spin u with a priori weight Phi in the magnetic field h**.
- Critical line Re s = 1/2 is Re h = 0, the imaginary-field axis. In the fugacity zeta_LY = e^{-2h} this is the
  Lee-Yang circle |zeta_LY| = 1.
- The functional equation xi(s) = xi(1 - s) is h -> -h: spin-flip symmetry (Phi even).
- **RH is equivalent to the Lee-Yang property of this single spin.** The structure is "no zeros for Re h > 0, plus
  spin flip". That is exactly the structure of the Lean RH proof's last step, `Claim.strip`: no zeros right of 1/2,
  plus the functional equation.

**What the Yang-Mills machinery provides here.** The OS layer (`ProofPhase/OS`, `M1/UVTVOS.lean`) and the bridge
(`Bridge/Spectral.lean`, `Bridge/OSLink.lean`) turn *weight positivity plus locality* into a Hilbert space, a positive
transfer operator, and spectral statements: Hankel (Euclidean) positivity. For the Lee-Yang route this machinery would
handle the existence of the lattice system, its block-spin limit and its positivity. It does not produce the
Lee-Yang property: that is a positivity of couplings (ferromagnetism), which must be put into the lattice system at
the start. The owner's "running as content" would be exactly this: a lattice system, run by its transfer matrix,
whose block spin has law Phi **[reading]**.

**Asano on the Euler factors, real place included** **[proved here]**:
- In the variables w_p = p^{1/2 - s} the critical line is the torus |w_p| = 1 for all p. The local factor
  (1 - p^{-1/2} w_p)^{-1} is holomorphic and zero-free on the closed polydisc |w_p| <= 1; its only singularity is a
  pole at |w_p| = p^{1/2} > 1. The Gamma factor pi^{-s/2} Gamma(s/2) is zero-free everywhere.
- So **no local factor has a zero**: neither in a Lee-Yang position nor anywhere else. Asano contraction controls
  where the zeros of a product of zero-carrying multi-affine factors go; with zero-free factors there is nothing to
  contract.
- The semilocal symbols of SEMILOCAL.md 3a say the same in the frequency variable. Each prime's weight has mean zero,
  so each local factor is neutral on the critical line, and the real place supplies only the mean density. The zeros
  of xi, and the positivity of Weil's form, are collective: the semilocal test needed every prime up to e^{2a} at
  once, and dropping one gave an order-one negative eigenvalue. That is the opposite of Lee-Yang's local-to-global
  mechanism **[numerical]** (SEMILOCAL.md) + **[proved here]**.
- The reciprocal 1/zeta has local factors (1 - p^{-s}) with zeros exactly on Re s = 0, the "Lee-Yang line" of each
  local variable. Their product keeps them there, but those zeros do not survive in 1/zeta (the product converges
  only for Re s > 1), and they are on the wrong line. The shift from 0 to 1/2 comes from the real place and the
  functional equation, not from any local factor **[proved here]**.

---

## 4. Step c: what is formalized

`ProofPhase/GRH/LeeYang.lean`, 8 theorems, standard axioms, 0 warnings **[Lean-ly]**:

| Theorem | Content |
|---|---|
| `lee_yang_identity` | \|1 + a z\|^2 - \|a + z\|^2 = (1 - a^2)(1 - \|z\|^2) |
| `lee_yang_pair` | A ferromagnetic bond factor 1 + a z + a w + z w (real \|a\| <= 1) has no zero with \|z\|, \|w\| < 1. |
| `asano_bound`, `asano` | **Asano contraction**: if A + B z + C w + D z w has no zero on the open bidisc, then A + D z has none on the open disc. The proof uses the parallelogram law at the points +-r to get \|D\| r <= \|A\|. |
| `chain3_ne_zero` | The three-spin chain, two bonds glued by one contraction, has no zero with all three \|z_i\| < 1. |
| `ising3_flip`, `ising3_zeros_on_circle` | Spin-flip symmetry z^3 Z(1/z) = Z(z); **every zero of the three-spin ferromagnetic chain's partition function lies on the unit circle.** |
| `pair_zeros_on_circle` | The same for one bond: the zeros of 1 + 2 a z + z^2 lie on \|z\| = 1. |

The general lattice is the same argument by induction over the bonds; it is not formalized. Not attempted: the heat
flow (de Bruijn's real-zero preservation needs the Laguerre-Polya theory of entire functions, which Mathlib does not
have).

---

## 5. Step d: the paper argument, step by step

1. **Dictionary.** xi(1/2 + h) = int Phi(u) e^{hu} du: one spin in field h; RH is the Lee-Yang property; the
   functional equation is spin flip. **[proved here]**
2. **Weight positivity.** Phi(u) > 0 for all real u (Polya; recalled) **[classical]**. It comes from the theta
   function, i.e. Poisson summation at the real place. This is the owner's "the real place carries existence", and
   it holds.
3. **Weight positivity is insufficient.** For t < 0 the weight e^{tu^2} Phi(u) is still positive, even and rapidly
   decreasing, but H_t has non-real zeros, because t < 0 <= Lambda (Rodgers-Tao). So no argument that uses only
   positivity of the weight (Hankel, Euclidean, reflection positivity of the weight) can prove RH. It would prove it
   for t < 0 too, which is false. **[classical]** for the inputs, **[proved here]** for the consequence.
4. **The needed extra property is ferromagnetic, at criticality.** The Lee-Yang class is closed under e^{tu^2},
   t >= 0. Phi is in the class (RH, now proved), e^{tu^2} Phi for t < 0 is not, so Phi is exactly at the boundary:
   Lambda = 0 is a critical coupling **[classical]** + **[Lean]**. In physics language, Phi must be the block-spin law
   of a *critical* ferromagnet. Newman's reading, recalled.
5. **Building the ferromagnet.** Three candidate sources:
   - **5a. The Euler product with Asano:** blocked, because the local factors are zero-free (section 3)
     **[proved here]**.
   - **5b. The primon gas / Bost-Connes:** a free gas; the zeros lie beyond its phase transition, outside the domain
     of its partition function (section 2) **[classical]**.
   - **5c. The theta side:** Phi is built from theta(x) = sum over n in Z of e^{-pi n^2 x}, formally the partition
     function of a discrete Gaussian spin, the real place's own object. The step would be: realise Phi(u) du as the
     block-magnetisation law of a ferromagnetic lattice system with Lee-Yang single-site measures and non-negative
     couplings, at its critical point, and conclude by Newman's closure. **No such representation is known. This is
     where the route stops.** **[open]**

**The blocking step, named as precisely as before:**

> **Step 5c.** Construct a lattice ferromagnet (Lee-Yang single-site measures, non-negative couplings, a
> reflection-positive transfer matrix) whose block-spin law converges to Riemann's Phi(u) du. Because Lambda = 0, the
> system must be at its critical coupling. Given such a system, Newman's closure theorems give the Lee-Yang property
> of Phi, i.e. RH, by a positivity mechanism. The Euler product cannot supply it (zero-free local factors), and the
> primon gas cannot either (zeros beyond its phase transition). The theta side is the only candidate source left.

**How it relates to ATTEMPT.md step 4.** It is the *same obstacle in a different, stronger form*. A Lee-Yang
representation implies RH (Newman), which implies Weil positivity (Weil), which gives step 4's Phi (GNS). It is not
weaker. It is more specific about what is missing: not a positive Hilbert-space structure as such, but a *coupling
positivity at criticality*, on the Euclidean side, where weight positivity is already available and provably
insufficient (step 3). Both routes agree that there is no slack. Weil's margin collapses super-exponentially with
the support (ATTEMPT.md section 4), and the de Bruijn-Newman margin is exactly zero.

**Nearest known finite approximants** (recalled, not re-read): the degree-d Jensen polynomials of xi's Taylor
coefficients are real-rooted for every d once the shift is large enough (Griffin, Ono, Rolen, Zagier 2019), with
Hermite polynomials as the limit. RH is equivalent to real-rootedness for all degrees and shifts. These are
"finite-volume" real-rootedness statements, but they come from asymptotics, not from a ferromagnetic construction
**[classical]**.

**Numerics.** None were run. Nothing on this route is decided by a few CPU-minutes: the margin is exactly zero, and
the obstacle is structural.

---

## 6. DMP readings (separate; not mathematics)

> **This section maps the owner's readings (PREP.md, last eight entries) onto the route. Nothing here is a
> mathematical result.**

- **"The real place carries existence."** *Exact correspondence.* The positive weight Phi > 0 comes from the theta
  function, i.e. Poisson summation at the real place (step 2); in the semilocal test the real place supplies the
  positive mean density. Existence (positivity) is there.
- **"The primes as free U(1) phases."** *Exact correspondence.* In the spin dictionary, each Euler factor is a
  zero-free function of the phase e^{-ih log p}. The phases move independently (log p are rationally independent),
  and no single phase pins a zero. The freedom is real, and so is its consequence: no local factor carries the line.
- **"Exists but never runs."** *Exact correspondence, and now precise.* Weight positivity (existence) holds for every
  t in the de Bruijn-Newman family. What makes the zeros real is a ferromagnetic structure, which would be the
  "running", and it has to sit exactly at the critical coupling t = 0. The arithmetic side exists at every t and is
  real-rooted exactly at the edge. A system that runs it there is what is missing (step 5c).
- **"Run as content in a DMP-complete system."** *Analogy, with a precise target.* The Yang-Mills system runs: a
  lattice, local couplings, a reflection-positive transfer matrix, a block-spin limit. Running zeta as content would
  mean a lattice ferromagnet whose block spin has law Phi, at criticality. The reading names the right kind of object;
  it does not supply the object.
- **Verdict:** the readings are **supported as a description**. Existence and running separate exactly into weight
  positivity (present, insufficient) and critical ferromagnetic coupling (absent). The readings **do not close** the
  step: no construction of the running system follows from them.

---

## 7. Files and references

**Files.** `docs/mass-gap/formal/ProofPhase/GRH/LeeYang.lean`; `docs/rh-guide/grh/axioms-leeyang.sh`, `.log`.

**References** (recalled unless noted).
- T. D. Lee, C. N. Yang, "Statistical theory of equations of state and phase transitions II. Lattice gas and Ising
  model", Phys. Rev. 87 (1952); T. Asano, "Theorems on the partition functions of the Heisenberg ferromagnets",
  J. Phys. Soc. Japan 29 (1970); D. Ruelle, *Statistical Mechanics: Rigorous Results* (1969), the contraction method.
- C. M. Newman, "Fourier transforms with only real zeros", Proc. AMS 61 (1976); C. M. Newman, "Zeros of the partition
  function for generalized Ising systems", Comm. Pure Appl. Math. 27 (1974); R. B. Griffiths, B. Simon, "The
  (phi^4)_2 field theory as a classical Ising model", Comm. Math. Phys. 33 (1973).
- N. G. de Bruijn, "The roots of trigonometric integrals", Duke Math. J. 17 (1950); B. Rodgers, T. Tao, "The de
  Bruijn-Newman constant is non-negative", Forum Math. Pi 8 (2020); D. H. J. Polymath, "Effective approximation of heat
  flow evolution of the Riemann xi function, and a new upper bound for the de Bruijn-Newman constant", Res. Math. Sci.
  6 (2019).
- B. Julia, "Statistical theory of numbers" (1990); D. Spector, "Supersymmetry and the Moebius inversion function",
  Comm. Math. Phys. 127 (1990); J.-B. Bost, A. Connes, "Hecke algebras, type III factors and phase transitions with
  spontaneous symmetry breaking in number theory", Selecta Math. 1 (1995).
- G. Polya, "Bemerkung ueber die Integraldarstellung der Riemannschen xi-Funktion", Acta Math. 48 (1926) (positivity
  of Phi); M. Griffin, K. Ono, L. Rolen, D. Zagier, "Jensen polynomials for the Riemann zeta function and other
  sequences", PNAS 116 (2019).
