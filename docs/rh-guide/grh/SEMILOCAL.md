# The semilocal Weil test: which places does positivity need?

Private working note, 2026-11-23. Follows `ATTEMPT.md` (step 2 of the GRH attempt). Question from the owner's reading
(PREP.md, "A second prime is always forced"): "for something real to exist, it has to at least have a partner to
assert itself against, so the minimum amount of primes is two." Test: cut Weil's form down to a finite set of places
S and see where it stays positive.

**Claim marks** as in `ATTEMPT.md`: **[numerical]** = computed by `semilocal.py` (output `semilocal.log`,
thresholds in `semilocal-thresholds.log`); **[classical]**; **[proved here]**; **[reading]**; **[open]**. Items
recalled from the literature rather than re-read in this session say so.

---

## 0. The answers

1. **Every finite S goes negative, and clearly so.** Weil's form cut to a finite set of places S, keeping the real
   place, stays positive only up to a support a(S) just above (1/2) log p* (0.03 to 0.04 above, section 3), where p*
   is the smallest prime *missing* from S. That is the moment the missing prime first enters the support of h = f * f~. Past that point the smallest
   eigenvalue is of order -0.1 to -8, far above the numerical noise (about 1e-10) **[numerical]**. With the real place
   alone, a({inf}) is (1/2) log 2 = 0.347, the range where Connes and Consani proved positivity (recalled)
   **[classical]**.
2. **Adding a prime helps only if it is the next prime.** {inf, 2} is positive up to (1/2) log 3 = 0.549; adding 3
   restores positivity there and carries it to (1/2) log 5 = 0.805; adding 5 carries it to (1/2) log 7 = 0.973; adding
   7 carries it to about (1/2) log 11 = 1.199. A prime that is not next does nothing for positivity: {inf, 3} and
   {inf, 5} fail at the same place as {inf} (2 is missing), and {inf, 2, 5} fails at the same place as {inf, 2}
   (3 is missing). So two primes are not enough in general; {inf, 3, 5} is worse than {inf, 2}. What counts is
   **completeness up to the scale**: every prime p <= e^{2a} must be in S **[numerical]**.
3. **Minimal S that behaves like the full form:** on support [-a, a] it is S_a = {inf} together with every prime up
   to e^{2a}. With that S the cut form *is* the full form, since the missing primes' terms vanish identically
   **[proved here]**, and it shows the full form's positivity with its super-exponentially collapsing margin. No
   finite S matches the full form at all supports. The real place cannot be dropped: {2, 3} without it is negative at
   every support, even before any prime enters **[numerical]**.

---

## 1. The test

Weil's form for zeta, in the conventions of `weil_numerics.py` (normalisation checked against the zeros to 1e-16).
Here h = f * f~, F is the transform of f, and f is supported in [-a, a]:

  W_S(f) = POLE + [REAL if inf in S] - sum over p in S, k >= 1, of log(p) p^{-k/2} [h(k log p) + h(-k log p)],
  POLE = 2 F(i/2) F(-i/2),   REAL = -log(pi) h(0) + (1/2pi) int |F(r)|^2 Re psi(1/4 + ir/2) dr.

The pole terms are always kept: they belong to the completed zeta function, not to a place. "lambda_min" is the
smallest value of W_S(f) / int f^2 over the span of (1 - t^2)^2 P_j(t), t = x/a, with P_j the Legendre polynomials,
j < 10 (and j < 6 as a check). It is computed at two accuracy levels: coarse (600 nodes, 60001 frequency points, cut-off
400/a) and fine (1200, 200001, 800/a). Sets tested: {inf}, {inf,2}, {inf,3}, {inf,5}, {inf,2,3}, {inf,2,5}, {inf,3,5},
{inf,2,3,5}, {inf,2,3,5,7}, all places, and {2,3} without the real place. Supports a from 0.15 to 2.5. CPU time:
7 minutes for the scan. The threshold bisection took longer than planned, because other jobs shared the machine.

**{2, 3} without the real place.** It can be computed, but it is not a sensible positivity candidate. Without the
real place the form has no term that controls int |f|^2: what remains is the rank-two pole term (one negative
direction) plus the indefinite prime terms. It is negative at every a (lambda_min = -1.0e-3 at a = 0.15, before any
prime enters; -0.45 at a = 0.45) **[numerical]**.

---

## 2. Results

Smallest eigenvalue, fine accuracy, 10 basis functions (from `semilocal.log`). "+" values below about 1e-10 are noise
level; the full table with the coarse and 6-function columns is in the log.

| a | primes p <= e^{2a} | {inf} | {inf,2} | {inf,3} | {inf,2,3} | {inf,2,3,5} | {inf,2,3,5,7} | all |
|---|---|---|---|---|---|---|---|---|
| 0.25 | none | 4.2e-2 | 4.2e-2 | 4.2e-2 | 4.2e-2 | 4.2e-2 | 4.2e-2 | 4.2e-2 |
| 0.3466 | 2 (edge) | 1.9e-3 | 1.9e-3 | 1.9e-3 | 1.9e-3 | 1.9e-3 | 1.9e-3 | 1.9e-3 |
| 0.45 | 2 | **-0.17** | 3.4e-5 | **-0.17** | 3.4e-5 | 3.4e-5 | 3.4e-5 | 3.4e-5 |
| 0.55 | 2, 3 (edge) | **-0.39** | 3.7e-7 | **-0.39** | 3.7e-7 | 3.7e-7 | 3.7e-7 | 3.7e-7 |
| 0.70 | 2, 3 | **-0.69** | **-0.43** | **-0.49** | 2.6e-9 | 2.6e-9 | 2.6e-9 | 2.6e-9 |
| 0.85 | 2, 3, 5 | **-0.97** | **-0.63** | **-0.51** | **-0.060** | noise (+) | noise (+) | noise (+) |
| 1.00 | 2, 3, 5, 7 (edge) | **-1.26** | **-0.95** | **-0.89** | **-0.61** | noise | noise | noise |
| 1.25 | 2, 3, 5, 7, 11 | **-1.80** | **-1.56** | **-1.47** | **-1.19** | **-0.68** | **-1.0e-3** | noise |
| 1.50 | up to 19 | **-2.48** | **-2.37** | **-2.11** | **-2.02** | **-1.60** | **-1.28** | noise (+) |
| 2.50 | up to 148 | **-8.1** | **-8.5** | **-8.2** | **-8.5** | **-8.4** | **-8.1** | noise |

Reading the table **[numerical]**:
- In each column the values agree with "all" exactly, to every printed digit, while S still contains every prime
  below e^{2a}. They drop to order -0.1 or below as soon as one such prime is missing.
- The negative values are stable across accuracy levels and basis sizes; for example {inf,2} at a = 0.7 gives -0.4303
  (coarse), -0.4303 (fine) and -0.3626 (6 functions). They are not noise.
- The only borderline entries are where the missing prime sits at the very edge of the support, so its term is tiny.
  {inf,2,3,5} at a = 1.0 has 2a = 2 just above log 7 = 1.946, and gives -7.5e-10 with 10 functions and +8.4e-8 with 6.
  The threshold bisection (section 3) resolves these.
- {inf,2,5} equals {inf,2} at every a up to 0.7 (3 missing). {inf,3,5} equals {inf} up to 0.45 (2 missing). A prime
  above the gap changes nothing until the gap is filled.

## 3. The thresholds a(S)

Bisection for the first support at which lambda_min < -1e-6 (fine accuracy), compared with (1/2) log p*
(`semilocal-thresholds.log`, `semilocal-thresholds-2.log`; run as `py semilocal.py --thresholds` and `--thresholds 3`) **[numerical]**:

| S | first missing prime p* | (1/2) log p* | a(S), 10 basis functions | a(S), 6 basis functions |
|---|---|---|---|---|
| {inf} | 2 | 0.3466 | 0.3841 | 0.3956 |
| {inf,3} | 2 | 0.3466 | 0.3841 (same as {inf}) | 0.3956 |
| {inf,2} | 3 | 0.5493 | 0.5765 | 0.5941 |
| {inf,2,3} | 5 | 0.8047 | 0.8364 | 0.8411 |
| {inf,2,3,5} | 7 | 0.9730 | 1.0029 | 1.0178 |
| {inf,2,3,5,7} | 11 | 1.1990 | 1.2343 | 1.2472 |

- **Every threshold sits just past the point where the first missing prime enters the support of h**: 0.03 to 0.04
  above (1/2) log p* with 10 basis functions, and closer as the basis grows (the 6-function values are always larger).
  So the cut form fails essentially as soon as the missing prime's terms become non-zero. The short delay is the time
  h(log p*) needs to grow from zero at the edge of its support to the size of the full form's (tiny) margin.
- {inf,3} has exactly the threshold of {inf}: the prime 3 contributes nothing while 2 is missing.
- This resolves the borderline entries of section 2: {inf,2,3,5} at a = 1.0 is still positive (threshold 1.003), so
  the -7.5e-10 there was quadrature noise.

## 3a. The places seen from the zeros' side: one symbol per place

Weil's form can be read entirely in the frequency variable r, which is where the imaginary parts gamma of the zeros
sit (the zero side is sum over zeros of |F(gamma)|^2). For full support each place v contributes a weight
("symbol") phi_v(r) = 2 Re (L_v'/L_v)(1/2 + ir), the real part of its local log-derivative on the critical line:

  W_S(f) = POLE + (1/2pi) int |F(r)|^2 [sum over v in S of phi_v(r)] dr     **[classical]**, by summing the k-series.

For finite support only the prime powers with k log p < 2a enter (section 1); the symbols describe the full picture.
From `semilocal-symbols.log` **[numerical]**, with exact formulas **[proved here]**:
- **A prime p gives a periodic weight in r**, of period 2pi / log p (9.06 for p = 2, 5.72 for p = 3). Its mean is
  exactly 0 and its range is [-2 log p q/(1-q), +2 log p q/(1+q)], q = p^{-1/2}: [-3.35, 0.57] for 2, [-3.00, 0.80]
  for 3.
- **Two primes give a quasi-periodic weight.** phi_2 + phi_3 depends on the two phases (r log 2, r log 3) mod 2pi.
  Since log 2 / log 3 is irrational (2^m = 3^n has no solution with m, n >= 1), the line r -> (r log 2, r log 3) fills
  the 2-torus densely (Kronecker): the weight never repeats, and along r it comes arbitrarily close to every value it
  takes on the torus. Numerically, on [0, 1e6] its mean is 2e-6 (exact value 0) and its range [-6.3483, 1.3785] equals
  the torus range to four digits.
- **The real place gives the growing mean.** phi_inf(r) = -log pi + Re psi(1/4 + ir/2) equals log(r / 2pi) to four
  digits from r = 14 on (0.8102 against 0.8104 at r = 14.13; 9.6750 at r = 1e5). Divided by 2pi this is the average
  density of the zeros' imaginary parts (Riemann-von Mangoldt: N(T) ~ (T/2pi) log(T/2pi e)) **[classical]**. The
  primes add only the fluctuations around it (the S(T) term, built from prime phases) **[classical]**.

So **{2, 3} without the real place** is a weight with mean zero living purely on the frequency axis. A form with mean
weight zero cannot be positive once the test functions resolve its negative parts. Before any prime enters, what
remains is the rank-two pole term, which has a negative direction. This is why the numbers in section 2 are negative
at every support **[proved here]** for the mechanism, **[numerical]** for the values.

## 4. What this says

- **Positivity is not local.** Each prime's terms are indefinite on their own (ATTEMPT.md, section 5). Positivity of
  the form on [-a, a] needs the real place, the pole terms, and every prime up to e^{2a}, together. Leave out one
  prime inside the range and the form is not slightly negative but clearly negative. The cancellation that keeps the
  full form positive (with a margin collapsing to 1e-9 and below) is a cancellation among *all* the places in range
  **[numerical]**, **[reading]** for "cancellation among all places".
- **This sharpens the open step of ATTEMPT.md.** A positive object Phi with <Phi f, Phi f> = W(f * f~) cannot be built
  place by place, or from a fixed finite set of primes. At scale a it must see every prime up to e^{2a} at once. The
  Euler product does carry all primes at once, which is one more reason it is the natural candidate. Its sign problem
  remains (ATTEMPT.md, section 5, step 4) **[reading]**.
- **Literature (recalled, not re-read).** Connes and Consani proved positivity of the archimedean (S = {inf}) Weil form
  for test functions supported in [2^{-1/2}, 2^{1/2}] on the multiplicative scale, that is |x| <= (log 2)/2 here. The
  {inf} column fits this. The numerical threshold for {inf} is a = 0.384 with 10 basis functions (0.396 with 6), and it
  drops as the basis grows, so the true threshold lies between 0.347 and 0.384. The proved bound is within about 11%
  of it. Connes's semilocal trace formula (1999) realises
  W_S for finite S as a trace on a semilocal adele class space; positivity there is not expected for fixed S, which
  fits answer 1 **[classical]**.

---

## 5. DMP reading (separate; not mathematics)

> **The owner's reading (PREP.md): "for something real to exist, it has to at least have a partner to assert itself
> against, so the minimum amount of primes is two." This section says plainly what the test shows about it.
> Nothing here is a mathematical result.**

- **On "the minimum amount of primes is two": the test contradicts it as a fixed number.** How many primes positivity
  needs depends on the scale:
  - none up to a = 0.347 (the real place with the poles suffices);
  - one (the prime 2) up to 0.549;
  - two (2 and 3) up to 0.805;
  - three up to 0.973, and so on.

  Two primes are enough only in the window 0.549 < a < 0.805, and only if they are 2 and 3. Two other primes ({3, 5},
  {2, 5}) do worse than 2 alone. No finite number suffices at all scales.
- **On "a partner to assert itself against": the test is consistent with it in a weaker form.** No place stands alone:
  - primes without the real place are never positive, not even before they enter;
  - the real place alone fails as soon as the first prime is in range;
  - each prime asserts itself only together with all smaller primes.

  So "existence needs a partner" holds here as "positivity needs the real place plus the complete set of primes below
  the scale": a chain of partners, filled in order, not a pair. *Analogy*.
- **Verdict:** **contradicts** the specific claim that two primes are the minimum; **neutral to mildly supportive** of
  the general reading that nothing exists alone. The partner of a prime turns out to be all primes below it plus the
  real place, not one other prime.

**The owner's addition: "Two primes without the real places might be the possibility space that is spanned by the
imaginary component, that builds in the dualistic system well."** Mapped onto section 3a (the imaginary parts gamma of
the zeros are the frequencies Weil's form evaluates at; the real place carries the Gamma factor):
- **Exact correspondence, and here "two" is special.** Without the real place, the primes act only on the frequency
  axis, the imaginary direction. One prime gives a periodic pattern in gamma (period 2pi / log p), a closed circle of
  phases. **Two primes are the first case that never repeats**: the phases (gamma log 2, gamma log 3) fill a 2-torus
  densely, so as gamma runs, every phase combination is approached (section 3a, numbers to four digits). A genuinely
  two-dimensional space of possibilities, spanned as the imaginary part runs, needs at least two primes. This supports
  "minimum two" in the sense of *non-repeating structure in the imaginary direction*. **[proved here]** (Kronecker plus
  the irrationality of log 2 / log 3).
- **Contradicted as positivity, or as existence on its own.** That space has mean weight exactly zero and is negative
  at every support tested. Positivity (in the owner's earlier reading, "something exists") appears only when the real
  place is added, which carries the Gamma factor and with it the positive average density log(gamma / 2pi) of the
  zeros. So the two-prime space does not "build well" by itself: it is the fluctuation, and the real place is the
  mean that makes a positive density possible.
- **"Dualistic system".** The numbers fit a split in two: a real-place part (smooth, growing, positive mean: where the
  zeros are on average) and a prime part (oscillating, mean zero: where exactly they sit). Only the two together are
  positive. *Analogy* for "dualistic"; the split itself is the classical Riemann-von Mangoldt split of N(T) into its
  smooth term and S(T).
- **Verdict on the addition:** **supported** as a description of what two primes span (a non-repeating 2-torus of phases
  in the imaginary direction, the smallest such case); **contradicted** if it means that this space is positive or
  stands without the real place; the real place is its necessary partner.
