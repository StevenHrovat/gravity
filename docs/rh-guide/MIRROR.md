# The mirror tool: 8 pi^2 = -4 zeta(2) / zeta(-1) across the three problems

Private working note, 2026-11-23, an exploratory round approved by the owner ("Perfect to attack all three with as a
new tool!"). The source is PREP.md's last two entries. The owner wrote that 8 pi^2 is "simplified by the correlation
of Euler's number and the zeta function ... And then again simplified by the inherent dualistic properties". The
coordinator read this as the identity 8 pi^2 = -4 zeta(2) / zeta(-1), which is the functional equation of zeta at
s = 2.

**Honest framing (kept throughout).** As mathematics the identity is a **rewriting**: Euler's zeta(2) = pi^2/6
together with the reflection s <-> 1 - s. Its possible value as a tool is that it pairs a UV constant with an IR
constant across the mirror:
- **UV:** the instanton cost 8 pi^2 / g^2.
- **IR:** zeta(-1) = -1/12, the coefficient of the Luescher term of the flux tube, the universal string correction.

This note tests whether that pairing carries content in each problem.

**Claim marks:**
- **[numerical]** = `mirror.py` (output `mirror.log`, under a second);
- **[classical]** = known; "recalled" means recalled, not re-read in this session;
- **[proved here]** = argued in this note;
- **[Lean]** = `ProofPhase/GRH/Mirror.lean`, 3 theorems, standard axioms only (`grh/axioms-mirror.log`);
- **[reading]** = interpretation;
- **[open]** = not settled.

---

## 0. The answers

1. **The identity is the k = 1 member of a family, and Lean derives it from Mathlib's functional equation.**
   - **The family:** (2 pi)^(2k) = 2 (-1)^k (2k-1)! zeta(2k) / zeta(1 - 2k) for every k >= 1 **[classical]**. At k = 1
     it reads 8 pi^2 = 2 (2 pi)^2 = -4 zeta(2) / zeta(-1). Every power pi^(2k) can be written this way, so the identity
     singles out nothing beyond k = 1.
   - **In Lean:** `riemannZeta_one_sub` at s = 2 gives zeta(-1) = -2 (2 pi)^-2 zeta(2). With `riemannZeta_two` this
     gives 8 pi^2 = -4 zeta(2) / zeta(-1) and zeta(-1) = -1/12 **[Lean]**.
   - **Where the shared 2 pi comes from:** the (2 pi)^2 in the instanton action and the (2 pi)^-s in the functional
     equation are the same normalisation, the 2 pi of e^(2 pi i). In the instanton it enters through Chern-Weil
     integrality; in the functional equation through the Fourier transform. That is a shared normalisation, not a
     dynamical link.
2. **Yang-Mills: the pairing is real as two asymptotic ends of F_e(L), and it says nothing in between, where the
   open quantity sits.**
   - **IR end:** in the effective-string regime the Luescher term (zeta(-1)) lowers F_e(L) by the universal amount
     pi (d - 2)/6 = 1.047.
   - **What the one-box condition becomes:** F_e(L) > log mu_4 = 1.91 turns into L sqrt(sigma) > 1.72 (Luescher) or
     > 1.80 (Arvis's closed-string formula). That is just above the effective string's breakdown point
     L sqrt(sigma) = 1.45. **[numerical]**
   - **UV end:** in small twisted boxes, semiclassics (fractional instantons, cost 4 pi^2 / g^2) makes electric flux
     cheap. F_e is exponentially small there.
   - **The closest known UV-IR relation:** on R^3 x small S^1, where confinement is semiclassical, the string tension
     is a power of the fractional-instanton weight (Uensal-Yaffe and successors, recalled). That holds only at small
     circle size.
   - **So the mirror brackets F_e(L) between two expansions and leaves the crossover untouched.** It does not
     constrain F_e at one box. **[proved here]** for the arithmetic, **[reading]** for "brackets".
3. **GRH: it is the duality we already have.**
   - **The mirror pair Weil's form actually uses is (s = 1, s = 0)**, not (2, -1). It fixes the real-place constants
     log pi + gamma and the pole terms; zeta'(0)/zeta(0) = log 2 pi. **[numerical]**
   - **These constants belong to the archimedean part A alone,** and A on its own is indefinite from support 0.425 on
     (`grh/TRANSFER.md`). Davenport-Heilbronn has the same kind of constants and zeros off the line.
   - **No sign comes from it.** `krein_off_line` shows exactly this: duality allows the off-line pair.
     **[proved here]**
4. **P vs NP: no natural mirror pairing.** zeta(2) does occur: it is the k -> infinity limit of the PPSZ savings
   constant for k-SAT (recalled). But it occurs on the algorithm (upper-bound) side only. Its mirror zeta(-1) plays no
   role, and nothing links it to a lower bound.
5. **The stop:** in every problem, the tool rewrites a constant that already sits at one asymptotic end. The open
   quantity is in the middle:
   - in Yang-Mills, F_e(L) at the crossover box;
   - in GRH, the relative position of the primes and the real place;
   - in P vs NP, any lower bound.

---

## 1. The identity, exactly

**The functional equation [classical; Mathlib].** Mathlib's form (`riemannZeta_one_sub`) is
zeta(1 - s) = 2 (2 pi)^-s Gamma(s) cos(pi s / 2) zeta(s).
- **At s = 2:** Gamma(2) = 1 and cos(pi) = -1, so zeta(-1) = -2 (2 pi)^-2 zeta(2). Hence
  8 pi^2 = 2 (2 pi)^2 = -4 zeta(2) / zeta(-1) = 78.9568... **[Lean: `zeta_neg_one_mirror`, `eight_pi_sq_mirror`;
  numerical]**
- **At s = 2k:** (2 pi)^(2k) = 2 (-1)^k (2k-1)! zeta(2k) / zeta(1 - 2k). This is checked for k = 1 to 4 to 20 digits
  in `mirror.log`. The values zeta(1 - 2k) = -B_2k / (2k) are rational (Bernoulli), and the values zeta(2k) are
  rational multiples of pi^(2k).

**What it is [proved here].** The identity contains exactly Euler's evaluation plus the reflection. On one side,
zeta(2k) is an absolutely convergent Euler product over the primes. On the mirror side, zeta(1 - 2k) is a regularised
value, the same one that zeta regularisation assigns to the divergent sum of n^(2k-1). The pairing is "convergent
prime product <-> regularised Casimir sum". That is a genuine structural feature of zeta, but it attaches to every
k equally.

**Where 8 pi^2 comes from in Yang-Mills [classical].**
- **The Bogomolny bound:** S >= 8 pi^2 |Q| / g^2, with Q = (1 / 8 pi^2) times the integral of tr F wedge F, the second
  Chern number.
- **The factor 8 pi^2 = 2 (2 pi)^2:** the (2 pi)^2 is the integrality normalisation of curvature (F / 2 pi has
  integral periods), squared because the second Chern character is quadratic. The 2 is the 1/2 in ch_2 = tr(F^2)/2.
- **The functional equation's factor 2 (2 pi)^-s:** this is the normalisation of the Fourier transform (e^(2 pi i x y))
  and of the Gamma factor.
- **So the match at s = 2 is a match of normalisations,** the 2 pi of the circle group in both. **[reading]**

---

## 2. Yang-Mills: UV instanton against IR string, and the one-box quantity

**The IR side: the Luescher term [classical, recalled].**
- **Where zeta(-1) enters:** a flux tube of length L has d - 2 transverse modes. Their zero-point energy, regularised
  by zeta, is (d - 2)(1/2) times the sum over n of (frequency 2 pi n / L), counting both movers for a closed loop.
  That gives (d - 2)(2 pi / L) zeta(-1) = -pi (d - 2) / (6 L). (For an open string between static charges it is
  -pi (d - 2) / (24 r).)
- **The closed-string ground state (Arvis, Nambu-Goto):** E_0(L) = sigma L sqrt(1 - pi (d - 2) / (3 sigma L^2)),
  which expands to sigma L - pi (d - 2) / (6 L) - ...
- **The UV side: the instanton [classical, recalled].**
  - **The classical cost:** the Bogomolny bound, 8 pi^2 / g^2 per unit charge, or 4 pi^2 / g^2 for a fractional
    charge in a twisted box.
  - **The one-loop determinant ('t Hooft):** it is regularised through the spectral zeta function of the fluctuation
    operator (zeta_Delta'(0)). By conformal invariance it reduces to harmonic analysis on S^4. Its constant is
    usually written with the Glaisher-Kinkelin constant, i.e. through zeta'(-1) (recalled, not re-checked).
  - **So both ends use zeta regularisation,** but of different objects: Riemann's zeta(-1) for the string modes, and
    an operator's zeta_Delta'(0) for the instanton. Only through the polynomial eigenvalue structure of S^4 do values
    of Riemann's zeta (derivatives at negative integers) enter the latter.

**Is there a relation in which the two are mirror images? [classical, recalled + reading]**
- **The closest known relation is semiclassical confinement on R^3 x S^1 with a small circle:** deformed Yang-Mills
  and adjoint QCD (Uensal-Yaffe; Poppitz-Schaefer-Uensal).
  - There, monopole-instantons, which are fractional instantons with action 8 pi^2 / (g^2 N), generate a mass gap and
    an area law.
  - The string tension is exponentially small in that action, so an IR constant (sigma) is a power of a UV weight.
  - This is a genuine UV-IR link. It holds where the circle is small and the coupling weak; continuity to R^4 is
    conjectured.
- **Resurgence (renormalons against instanton-antiinstanton pairs) relates the UV perturbative series to
  non-perturbative weights.** It is a relation between expansions, not a bound at finite size.
- **The mirror identity itself is not among these relations.** No known derivation produces zeta(2) <-> zeta(-1) as
  the map from the instanton cost to the Luescher term. **[reading]**

**Does it constrain F_e(L) at one box? [numerical + proved here]** (`mirror.log` part 3; d = 4, and
F_e(L) ~ L E_0(L) in the effective-string regime):

| form | F_e(L) | F_e > log mu_4 = 1.91 needs |
|---|---|---|
| Luescher | sigma L^2 - pi/3 (shift 1.047, universal) | sigma L^2 > 2.96, L sqrt(sigma) > 1.72 |
| Arvis | sigma L^2 sqrt(1 - 2 pi / (3 sigma L^2)) | sigma L^2 > 3.23, L sqrt(sigma) > 1.80 |
| breakdown (tachyon) | undefined below sigma L^2 = 2 pi / 3 | L sqrt(sigma) = 1.45 |

- **The IR side:** the mirror's IR constant converts the one-box condition into "the box is at least 1.8 string
  lengths". That holds only if the effective string applies there, and the condition sits just above its breakdown
  point. It also uses sigma > 0, which is confinement, the property being proved.
- **The UV side:** in small twisted boxes the electric flux energy is a tunnelling amplitude, exponentially small in
  the fractional-instanton action ('t Hooft; van Baal; recalled). There F_e is far **below** 1.91.
- **So the two mirror constants give the two asymptotic ends:** F_e is about 0 in small boxes, and
  sigma L^2 - pi/3 in large ones. The condition F_e > 1.91 sits in the crossover between them (`PROOF-BLUEPRINT.md`
  P4), where neither expansion is controlled.
- **Hence no constraint on F_e(L) at one box follows.** That is the first unclosable step for Yang-Mills, and it is
  the step that was already open (`CONTAINMENT.md`).
- **The project's own number:** the measured F_e(6) = 2.6 at beta 2.3 (`CONTAINMENT.md`) is consistent with the
  condition. Comparing it with the effective-string formula would need sigma in lattice units at that beta, and that
  comparison was not made here.

---

## 3. GRH: the mirror is the functional equation itself

**The mirror pair that Weil's form uses [classical + numerical].**
- **The constants of the explicit formula come from the pole at s = 1 and its mirror s = 0:**
  - At s = 1: residue 1 and the Laurent constant gamma.
  - At s = 0: zeta(0) = -1/2 and zeta'(0) = -(1/2) log 2 pi. The functional equation maps the data at s = 1 to these;
    gamma cancels against Gamma'(1) = -gamma, and zeta'(0)/zeta(0) = log 2 pi.
  - Together with pi^(-s/2) from the Gaussian, these give the real-place constant log pi + gamma = 1.7219 and the
    pole terms of `induction.py`'s functional. **[numerical: `mirror.log` part 2]**
- **The pair (2, -1) plays no structural role in Weil's form.** zeta(2) appears only inside the digamma expansions of
  the real-place kernel.

**Does reading these constants as mirror pairs give anything for the sign? [proved here]** No.
- **They are fixed by the duality and the normalisation of the real place:** that is, by the functional equation,
  which `TATE.md` showed allows off-line zeros.
- **They live in the archimedean part A** (pole + real place). `TRANSFER.md` part 3 showed that A on its own is
  indefinite from support 0.425 on, and that the sign is a property of the **relative position** of A and the
  primes, to 1e-9.
- **Davenport-Heilbronn has constants of the same kind** (its own Gamma factor and conductor) and zeros off the line.
- **This is exactly `krein_off_line`:** the duality is preserved, and the off-line pair exists.

---

## 4. P vs NP: is there a natural Mellin or zeta structure?

**Plainly: not one that links an upper and a lower bound.** What exists [classical, recalled]:
- **The PPSZ algorithm for k-SAT** (Paturi, Pudlak, Saks and Zane) runs in time 2^((1 - mu_k / (k - 1)) n), with
  mu_k = (sum over j >= 1 of) 1 / (j (j + 1/(k - 1))). Its limit as k -> infinity is the sum of 1/j^2 = zeta(2).
  For k = 3, mu_3 = 4 - 4 log 2, which gives about 2^(0.386 n).
  - So zeta(2) is the asymptotic savings constant of the best-known k-SAT algorithm.
  - It sits on the **upper-bound** side. The finite-k constant is a digamma value, not a zeta value at a mirror
    point. zeta(-1) has no role.
  - Hard instances for PPSZ itself bound that algorithm's running time from below. They are algorithm-specific, not
    complexity lower bounds.
- **Mellin transforms in the analysis of algorithms** (Flajolet's method for digital trees and divide-and-conquer
  recurrences) produce poles on vertical lines and periodic fluctuations. They describe average running times, not
  lower bounds.
- **Satisfiability thresholds** (2^k log 2 - (1 + log 2)/2 + o(1), Ding-Sly-Sun) come from moment and cavity methods,
  with no zeta structure.

So the mirror tool has no foothold in P vs NP beyond the appearance of zeta(2) as an algorithmic constant.

---

## 5. Lean

`ProofPhase/GRH/Mirror.lean` builds clean, with no warnings in the file. `grh/axioms-mirror.log` shows propext,
Classical.choice and Quot.sound only:
- `zeta_neg_one_mirror`: zeta(-1) = -2 ((2 pi)^2)^-1 zeta(2), from `riemannZeta_one_sub` at s = 2.
- `eight_pi_sq_mirror`: 8 pi^2 = -4 zeta(2) / zeta(-1).
- `zeta_neg_one_val`: zeta(-1) = -1/12, derived from the mirror and zeta(2) = pi^2/6. It agrees with Mathlib's
  Bernoulli formula.

The general family (k >= 1) needs the Gamma and cos values at s = 2k. It is routine and was left out.

---

## 6. Where it stops

**The tool rewrites constants that sit at the asymptotic ends; the open quantities sit in between [proved here]:**
- **Yang-Mills:** the mirror's UV constant (instanton cost) controls small boxes, and its IR constant (Luescher)
  controls long strings. The open quantity, F_e(L) > 1.91 at one box, is in the crossover. **[open]**, as before.
- **GRH:** the mirror is the functional equation. Its constants belong to the real place, and the sign is the
  relative position of the primes and the real place (`grh/TRANSFER.md`). It relates to the earlier faces as the
  duality face: `krein_off_line` and Davenport-Heilbronn. **[open]**, as before.
- **P vs NP:** no mirror structure links the two sides of a bound.

---

## 7. DMP reading (separate; not mathematics)

This section reads the owner's words against the mathematics above. Nothing here is a claim of the note.

- **"Simplified by the correlation of Euler's number and the zeta function":** at one loop, e and 8 pi^2 cancel into
  a scale ratio (PREP.md). The 8 pi^2 then becomes a ratio of zeta values across the mirror. The reading is exact as
  a rewriting: the cost of the first act (the instanton) is the mirror ratio of a convergent prime product, zeta(2),
  and a regularised Casimir sum, zeta(-1).
- **"The inherent dualistic properties":** the mirror pairs a prime-product side (convergent, analytic, a multiple of
  pi^2) with a Casimir side (regularised, rational, -1/12).
  - In the owner's language that is a pairing of the act's cost (UV) with the remnant's universal correction (IR,
    the Luescher term): both ends of a flux tube's life.
  - The pairing is real in the sense that both constants govern the two asymptotic ends of the same quantity F_e(L).
  - It does not reach the middle, where existence has to be certified at one box. That middle is where the open
    step has been all along.
- **For GRH:** the mirror is the functional equation itself: the link to G0 that is locally evaluable (`grh/TATE.md`).
  Reading the constants as mirror pairs adds no sign.
- **For P vs NP:** zeta(2) appears as the asymptotic saving of the best k-SAT algorithm. Its mirror has no
  counterpart there.
- **Verdict:** a good descriptive tool. It names the two ends (act cost and remnant correction) with one function.
  But in all three problems it is a rewriting at the ends, not a step in the middle.

---

## 8. Files and references

**Files:**
- `mirror.py`, `mirror.log` (this folder).
- `docs/mass-gap/formal/ProofPhase/GRH/Mirror.lean`, `grh/axioms-mirror.sh`, `grh/axioms-mirror.log`.

**References (recalled):**
- L. Euler, zeta(2); B. Riemann, functional equation;
- M. Luescher, K. Symanzik, P. Weisz (1980), string corrections; J. F. Arvis (1983);
- E. B. Bogomolny; G. 't Hooft (1976), instanton determinant; P. van Baal, twisted boxes;
- M. Uensal, L. Yaffe (2008); E. Poppitz, T. Schaefer, M. Uensal, semiclassical confinement on R^3 x S^1;
- R. Paturi, P. Pudlak, M. Saks, F. Zane (2005), PPSZ; P. Flajolet, Mellin transforms in the analysis of
  algorithms;
- J. Ding, A. Sly, N. Sun (2015), the k-SAT threshold.
