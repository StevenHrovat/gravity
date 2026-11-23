# The sign from the transferables: pairs, per-prime contraction, two-term bounds

Private working note, 2026-11-23. It follows `TATE.md` and the faces before it. The question comes from the
transfer round approved by the owner ("Start both transfer rounds, please").
- **The PREP.md entries since TATE:** the two categories of proof lines and the first true act as a combined pair;
  pairs of derived lines as the HTF's entanglement; the HTF smoothed to zero, with only remnants remaining.
- **Material from the other problems:** `docs/pnp/CP-DUALITY.md` (P vs NP), and `c9a-crossover/RDOEBLIN.md` and
  `HTF.md` (Yang-Mills).

The three questions:
1. Does a combined pair of prime steps carry a certificate that single steps do not?
2. Is "it runs" a per-prime contraction, and does the product of the per-prime coefficients converge?
3. Can Weil's form be bounded below by confinement x resolution?

As before, RH is proved (Lean) elsewhere in this repository, so the question is the mechanism.

**Claim marks** are as in `INDUCTION.md`:
- **[numerical]** = `transfer.py` (output `transfer.log`, 33 s), on the grid of `induction.py`;
- **[classical]** = known; "recalled" means recalled, not re-read in this session;
- **[proved here]** = argued in this note, on paper unless it says Lean;
- **[Lean]** = `ProofPhase/GRH/Transfer.lean`, 3 theorems, standard axioms only (`axioms-transfer.log`);
- **[reading]** = interpretation;
- **[open]** = not settled.

Notation: on a grid section, Weil's form is A + (sum over p of) P_p. Here A is the pole plus the real place, and P_p
is the block of the prime p, which carries all its powers (`TATE.md` section 3).

---

## 0. The answers

1. **Pairs: yes, the pair certifies what neither prime alone does. But it is the first case of an all-or-nothing
   rule, not a pairwise mechanism.**
   - **Combining steps gains nothing:** two Szego steps taken together carry exactly the product of the single steps.
     The positive extensions are parametrised by independent Schur parameters in the disk.
   - **Combining primes does:** at support 0.625 to 0.725 only the primes 2 and 3 are present. A + P_2 and A + P_3
     are both indefinite (lambda_min/t_0 = -0.23 to -0.88), while A + P_2 + P_3 is positive.
   - **The rule:** at every support computed beyond an entry window, the **only** positive set of primes is the full
     set present. At 1.225, dropping 11 (which has barely entered) already gives -1.1e-3 against +1e-9.
   **[numerical]**
2. **Per-prime contraction: it exists only on the finite sections, and there the roles are reversed.**
   - **On the constructed space the flow loses nothing:** on the Weil completion the scaling flow is an isometry
     (eta = 1, "flat"). What remains are the zeros (phases) and the orbit lengths log p: the explicit formula is a
     trace formula of these remnants.
   - **On the sections every step contracts:** the factors 1 - k^2 lie in (0.54, 1). The per-prime products are
     eta_2 = 0.065, eta_3 = 0.34, eta_5 = 0.49, eta_7 = 0.82 and eta_11 = 0.92 (r = 3, support up to 1.225).
   - **The product goes to zero:** this is Kolmogorov-Szego for the atomic zero measure.
   - **The reversal:** in Yang-Mills the wanted property is a uniform eta < 1, because the collapse is the gap. Here
     eta < 1 is automatic and the collapse is harmless. **The sign is eta_p > 0 at every step**: no factor may vanish.
   - **The grid problem returns in arithmetic form:** each factor depends on the whole history, with every smaller
     prime acting as a channel.
3. **Two-term bound: no bound that treats confinement and prime resolution separately can give the sign.**
   - **The best such bound is Weyl's,** lambda_min(A) + lambda_min(sum P): a bound that sees the two parts only
     separately cannot beat it, because aligning their worst directions attains it (Lean for the bound).
   - **It fails badly:** it is -7.9 t_0 against a true +1e-9 t_0 at support 1.225.
   - **The confinement term is itself not positive at resolvable scales:** lambda_min(A) < 0 from support 0.425 on.
     The growing mean log(r/2pi) confines only at frequencies above about 2 pi.
   - **The correct two-term form is Krein's extension theorem:** a section is positive exactly when Weil's
     distribution on the window extends to a positive measure. At small margin that measure is forced towards the
     atomic zero measure (Pisarenko). This, not a product, explains the 1e-9 tightness.
4. **The stop:** the step lemma in all-or-nothing form. At each scale, the full set of primes present, and no subset,
   must place the new corner entry inside the interval. No decomposition into pairs, single primes or two separate
   terms carries it. The eighth face (section 5).

---

## 1. Cuts as value: does a combined pair certify more?

**Combining two steps of the recursion [classical, recalled: Schur; Geronimus].**
- **The positive extensions are a product of disks:** given T_N > 0, the set of next two corner entries
  (t_{N+1}, t_{N+2}) with T_{N+2} > 0 is mapped bijectively onto the bidisk { |k_N| < 1, |k_{N+1}| < 1 }. The map
  is triangular: t_{N+1} fixes k_N, then t_{N+2} fixes k_{N+1}.
- **The margin is a product:** E_{N+2} / E_N = (1 - k_N^2)(1 - k_{N+1}^2) identically.
- **So a two-step certificate is exactly the product of the single-step ones.** In the Szego frame no "interval wider
  than the product" exists.

**Combining two primes inside a step [numerical]** (`transfer.log` part 1; r = 3, eps = 0.05; lambda_min / t_0 of
A + (sum over p in S of) P_p, for every subset S of the primes present):

| support | primes present | positive sets | examples of the other sets |
|---|---|---|---|
| 0.550 | 2, 3 | {2}, {2,3} | none: -0.65; {3}: -0.65 (3 has only just entered) |
| 0.625 | 2, 3 | **{2,3} only** | none: -0.93; {2}: -0.23; {3}: -0.84; {2,3}: +8.6e-8 |
| 0.725 | 2, 3 | **{2,3} only** | {2}: -0.85; {3}: -0.88; {2,3}: +2.2e-8 |
| 0.850 | 2, 3, 5 | {2,3,5} only | {2,3}: -0.065; {2,3,5}: +9.1e-9 |
| 1.025 | 2, 3, 5, 7 | {2,3,5,7} only | {2,3,5}: -0.18; best other: -0.18 |
| 1.225 | 2, 3, 5, 7, 11 | {2,3,5,7,11} only | {2,3,5,7}: -1.1e-3; the rest -0.99 to -3.2 |

- **The pair is the first certificate:** at supports 0.6 to 0.8 the pair {2,3} certifies positivity, and neither
  prime alone comes close. This is the literal form of the owner's "first true act": two derivations that share
  existence (the section) but not possibility (each alone is not positive).
- **It is not a pairwise structure:** the pair synergy lambda(A+P_2+P_3) - lambda(A+P_2) - lambda(A+P_3) + lambda(A)
  changes sign with the support (+0.44 at 0.725, -0.30 at 0.925). Once a third prime is present, no pair is
  positive. The rule is **all or nothing**: the certificate is carried by the full set of primes present, and
  dropping any one of them, including the newest, breaks it.
- **So pairs give no inductive leverage:** the pair at 0.6 to 0.8 is simply the full set at that scale. This
  sharpens the semilocal finding (`induction.log` part 2, dropping the newest prime) and `TATE.md` section 3
  (place by place): every proper subset fails, not only the single places.

**Relation to CP-DUALITY [reading].**
- **Where the analogy holds:** in cutting planes the pair channel (the interpolation split) is what makes lower bounds
  possible, and the cost is charged to the interface.
- **What the arithmetic analogue says:** the interface is the whole set. A certificate for the section exists only
  for the complete set of primes present. No smaller "interface" between groups of primes carries it.

---

## 2. Lossy DB and holonomy remnant: per-prime contraction

**On the constructed space: no loss, only remnants [classical + proved here].**
- **The flow is an isometry:** on the Weil completion (`TATE.md` section 2a, construction A), the scaling flow
  preserves the form exactly, so eta = 1.
- **A strict contraction is impossible there:** it would destroy the unitary spectrum that RH asserts. The field is
  "smoothed to zero" in the owner's sense: flat, nothing lost.
- **What remains is a trace formula (recalled: Weil; Guillemin; Connes; Deninger):**
  - Weil's explicit formula has the shape of a trace formula for a flow with closed orbits of length l = log p.
  - Each orbit and its k-th iterate carry weight l e^(-k l / 2), which is log p p^(-k/2): the length of the
    primitive orbit times the stability (holonomy-determinant) factor of a hyperbolic flow, as in the Selberg trace
    formula.
  - So the remnants are exact: zeros on the spectral side, orbit lengths log p on the geometric side, and nothing
    else.

**On the sections: per-step and per-prime contraction coefficients [numerical]** (`transfer.log` part 2; the margin
E_N / t_0 is the product of the Levinson factors 1 - k_m^2, grouped by which prime has a power at lag m):

| grid | archimedean-only lags | eta_2 | eta_3 | eta_5 | eta_7 | eta_11 | mixed lags | total E_N / t_0 |
|---|---|---|---|---|---|---|---|---|
| r = 3, to 1.225 | 0.12 (12 lags) | 0.065 (11) | 0.34 (6) | 0.49 (5) | 0.82 (3) | 0.92 (1) | 0.94 to 0.97 | 6.6e-4 |
| r = 1, to 1.225 | 0.34 (33 lags) | 0.94 (6) | 0.88 (4) | 0.99 (2) | 0.93 (2) | 0.93 (2) | none | 0.24 |

- **Every factor lies in (0, 1):** the smallest single-step factor is 0.54 (r = 3) and 0.87 (r = 1). So every step
  contracts, and no step comes near failing.
- **The product over all steps goes to zero [classical]:** this is Kolmogorov-Szego for the purely atomic zero
  measure (`VARIATIONAL.md` 1b). How the divergence splits between prime steps and archimedean steps cannot be
  decided from five primes. **[open]**, and not needed.
- **`prod_one_sub_le_exp` [Lean]:** losses c_i with divergent sum force the product to zero.

**The roles are reversed [proved here].**
- **Yang-Mills:** the chain argument (`RDOEBLIN.md`, `HTF.md`) needs eta <= eta_bar < 1, **uniformly**. The product
  going to zero is the desired decay, the gap.
- **The GRH induction:** eta_p < 1 is automatic, because the margin is monotone. The product going to zero is the
  harmless collapse. The danger is the opposite: a factor reaching 0 (|k| = 1), which would make the next section
  indefinite.
- **So "it runs" for GRH is "no factor vanishes",** a positivity of each factor (`margin_pos_of_factors`, Lean,
  template), not a uniform contraction.

**The grid problem in arithmetic form [proved here].**
- **In Yang-Mills:** the per-channel floor must be summed over the 2d faces of a box, and it misses by orders of
  magnitude (`RDOEBLIN.md` step 3).
- **Here:** a prime's factor 1 - k_m^2 has k_m = -(t_m - t^_m) / E_{m-1}, where t^_m is the extrapolation from
  **all** earlier lags. So every earlier prime is a channel into the step, and the number of channels grows without
  bound. No per-prime factor bound independent of the history exists in this frame.
- This is the history dependence of `INDUCTION.md` step 7, now in the language of the Yang-Mills chain.

**The sharpest transfer: in the hyperbolic analogue the sign is a mass gap [classical].**
- **Selberg zeta:** for a compact hyperbolic surface, the Selberg zeta function has its non-trivial zeros at the s with
  s(1 - s) = lambda_j, the Laplace eigenvalues.
- **"It runs" there:** the Laplacian is >= 0 and e^(-t Delta) is a contraction semigroup. That gives lambda_j >= 0,
  which puts the zeros **on the line or on the real segment (0, 1)**.
- **The zeros are on the line exactly when lambda_1 >= 1/4,** a spectral gap above the ground state.
- **"It runs" alone is not enough:** surfaces with small eigenvalues exist, so off-line real zeros occur. For
  congruence surfaces the 1/4 bound is Selberg's conjecture, still open; Kim-Sarnak's 975/4096 is the best known
  bound (recalled).
- **So in the one analogue where the operator is known, "it runs" (H >= 0) does not suffice, and the sign is
  literally a mass gap.** For zeta itself the operator is not known (Hilbert-Polya), and the transfer from Yang-Mills
  would have to supply the gap.

---

## 3. The two-term bound: confinement x resolution

**The confinement term [classical].**
- **The archimedean density:** the real place contributes the density (1/2pi)(Re psi(1/4 + i r/2) - log pi), which
  grows like (1/2pi) log(r/2pi). This is the Riemann-von Mangoldt density of zeros.
- **It is negative at low frequency:** about -0.86 at r = 0, crossing zero near r = 2pi.
- **The pole term grows like e^(u/2) in u = log x,** and the main term of the prime sum (the prime number theorem)
  cancels it exactly. What is left after that cancellation is the confinement density plus the prime fluctuation
  psi(x) - x.

**The best separated bound fails [numerical + proved here]** (`transfer.log` part 3, relative to t_0):

| support | lambda_min(A) (confinement) | lambda_min(sum P) (worst prime alignment) | Weyl bound | true lambda_min |
|---|---|---|---|---|
| 0.325 (no prime yet) | +0.014 | 0 | +0.014 | +0.014 |
| 0.425 | -0.12 | -0.59 | -0.71 | +2.9e-4 |
| 0.550 | -0.65 | -0.86 | -1.5 | +3.4e-7 |
| 0.850 | -1.7 | -2.1 | -3.9 | +9.1e-9 |
| 1.225 | -3.2 | -4.7 | -7.9 | +9.9e-10 |

The r = 1 grid gives the same picture: the Weyl bound is -2.8 against +8e-4 at 1.225.
- **Why no separated bound can work [proved here]:**
  - The bound lambda_min(A + P) >= lambda_min(A) + lambda_min(P) holds (`two_term_bound`, Lean).
  - No bound that depends only on the spectra of A and P separately can do better: rotating P so that its worst
    direction lies along A's worst direction attains it.
  - So the sign is a statement about the **relative position** of the archimedean and prime parts. It holds to a
    relative precision of 1e-9 to 1e-10, while each part on its own is negative by order 1.
- **The confinement term does not confine at the resolved scales:** a section resolves frequencies down to about 1/a,
  and there A is not positive. The growing mean acts only above r of about 2 pi, below the first zero (14.13), where
  the zero measure vanishes and the primes must cancel the archimedean term on average.

**The correct two-term form, and the 1e-9 [classical, recalled: Krein 1940; Pisarenko].**
- **Krein's extension theorem:** a positive-definite function on an interval (-2a, 2a) extends to a positive-definite
  function on the whole line. Applied to Weil's distribution, the section of support a is positive exactly when there
  is a positive measure mu_a on R whose Fourier transform equals Weil's distribution on (-2a, 2a).
- **The two terms of the certificate:** confinement is the mean density of mu_a (log(r/2pi) / 2pi), and resolution
  is the placement of its mass.
- **At the optimum the certificate is atomic:** the ground state's Pisarenko measure, N - 1 atoms on the line plus a
  uniform remnant lambda_min (`VARIATIONAL.md` 1a). Its atoms approximate the zeros.
- **This is what explains the tightness:** the zero measure is purely atomic, so the margin tends to zero
  (Kolmogorov-Szego). At a margin of 1e-9 the positive extension is nearly unique and nearly the zeros. A product
  bound with constants of order one cannot track a quantity that the certificate itself forces to zero.
- **Small-support positivity results are two-term bounds of this kind (recalled, not re-read: Yoshida; Bombieri;
  Connes-Consani).** They reach supports near where the first prime enters. That is consistent with `tate.log`, where
  the real place alone is positive up to about 0.35 to 0.4.

---

## 4. Lean

`ProofPhase/GRH/Transfer.lean` builds clean, with no warnings in the file. `axioms-transfer.log` shows propext,
Classical.choice and Quot.sound only:
- `prod_one_sub_le_exp`: for losses c_i in [0, 1], the product of the (1 - c_i) is at most exp(-(sum of c_i)). So
  contraction with divergent losses collapses the margin.
- `margin_pos_of_factors`: a positive start times positive factors stays positive. The sign concerns f_j > 0, not
  f_j < 1.
- `two_term_bound`: lower bounds add (Weyl). The sharpness, by aligning the worst directions, is argued in section 3
  and not formalised.

The Schur bidisk parametrisation (section 1) is classical. It needs the Levinson recursion in Lean, which is not
small, and it is not formalised.

---

## 5. Where it stops, and the relation to the earlier faces

**The stop:**
- **The first unclosable step:** at every scale, show from arithmetic alone that the full set of primes present
  places the new corner entry inside the extrapolated interval (|k| < 1).
- **The new constraint on any proof:** no subset of primes does it (part 1), no per-prime factor bound independent of
  the history exists (part 2), and no bound that separates confinement from prime resolution reaches it (part 3).
  A proof has to treat the primes as one set, in their exact relative position to the real place.
- **[open]**

**The earlier faces:**
1. **Weil Hilbert space:** its inner product is the all-or-nothing object; none of its subset truncations is positive.
2. **Critical ferromagnet:** Asano contraction adds one site at a time and works locally. Here one prime at a time
   fails, and so does any proper subset at a fixed scale.
3. **Deninger space:** in the hyperbolic analogue, geometric positivity (Laplacian >= 0) gives only "line or real
   segment". The line needs a gap (lambda_1 >= 1/4). A Deninger-type proof would have to supply the analogue of that
   gap, not only positivity.
4. **Hermite-Biehler chain:** Schur parameters are the per-step contraction coefficients. Combined steps are exactly
   products (part 1), so the chain has no hidden pair certificate.
5. **Step lemma:** this note's stop, refined to all-or-nothing.
6. **Sign of the remnant:** the same quantity. The certificate is Krein's positive extension, atomic at the optimum.
7. **Tate:** place-by-place assembly is impossible. Now subset-by-subset assembly is impossible too.

---

## 6. DMP reading (separate; not mathematics)

This section reads the owner's words against the mathematics above. Nothing here is a claim of the note.

- **"The first true act" as a combined pair:** literally visible. At the scale where only two primes exist, the pair
  certifies existence and neither single prime does. Beyond that, the certificate belongs to the whole set present.
  In the owner's terms: the act is not built from pairs. Once the system runs, every derived line takes part in
  certifying, and losing any one of them refutes the whole. That fits "pairs of derived lines as the entanglement",
  read as entanglement of the full set rather than of pairs.
- **"The HTF smoothed to zero, only remnants remain":** exact on the constructed space. The scaling flow there is
  flat (isometric), and the explicit formula is a trace formula of remnants only: the zeros, and the orbit lengths
  log p with their holonomy factors p^(-k/2).
- **"Lossy DB" and "it runs":** on the finite sections every step loses margin, which is the lossy DB, and the losses
  multiply to zero. That is not the danger. The arrow is kept as long as no single loss is total. So "it runs"
  means "no step loses everything", not "every step loses a fixed fraction". In the hyperbolic analogue this
  sharpens into a gap: running (H >= 0) puts zeros on the line or the real segment, and only a gap of 1/4 keeps them
  on the line.
- **"Confinement x resolution":** the confinement (the growing mean) acts only above the first zero's frequency. At
  the scales a section resolves, the arithmetic certifies existence by an exact cancellation, to 1e-9, between the
  real place and the full set of primes. The certificate is a positive measure that is nearly the zeros themselves.
- **Verdict:** each transferable has an exact counterpart and the numbers support the readings. Pairs are the first
  certificate, the remnants are a trace formula, and losses are automatic and harmless. None closes the step. The
  sign remains an all-or-nothing statement about the full set of primes at every scale.

---

## 7. Files and references

**Files:**
- `transfer.py`, `transfer.log`: subsets of primes, per-prime Levinson factors, and the Weyl two-term bound (33 s,
  mpmath 60 digits; reuses `induction.py`).
- `docs/mass-gap/formal/ProofPhase/GRH/Transfer.lean`, `axioms-transfer.sh`, `axioms-transfer.log`.

**References (recalled):**
- I. Schur; Ya. Geronimus, Schur parameters;
- M. G. Krein (1940), extension of positive-definite functions;
- V. F. Pisarenko (1973); Kolmogorov-Szego;
- A. Selberg, trace formula and the 1/4 conjecture; H. Kim, P. Sarnak (2003), 975/4096;
- V. Guillemin, A. Connes, C. Deninger, explicit formula as a trace formula;
- H. Yoshida; E. Bombieri; A. Connes, C. Consani, small-support positivity of Weil's functional.
