# A guiding idea for the Lean proof of the Riemann Hypothesis

Private working guide, 2026-11-23. It reads the proof released on 2026-11-20 by Levent Alpoege (a Lean library of
about 17 million lines, certified by the Lean and Mathlib communities on 2026-11-21) and asks: what is the one idea
that makes it work, and where does it meet what mathematicians already expected? Sources are in `SOURCES.md` and are
cited as S1, S2, ...

**Claim marks used throughout**

| Mark | Meaning |
|---|---|
| **[Lean]** | Proved in the Lean library; I read the statement or proof in the source myself (S4). |
| **[Lean, traced]** | Proved in the Lean library according to a community trace of the source (S5, S6), whose authors checked the declaration names against the exported list of what the final theorem uses. I did not re-read that file. |
| **[note]** | Stated in the author's 4-page note (S3). Informal, not a theorem. |
| **[classical]** | Known mathematics before this proof (S9). |
| **[reading]** | An interpretation, by community readers or by me. Names in the code are not evidence of meaning. |
| **[analogy]** | A structural likeness, not a mathematical result (used mainly in the DMP section). |
| **[open]** | Not settled, or not checked by anyone I could find. |

---

## 1. What exactly is proved

Five theorems in `src/Main.lean` (S2, S4) **[Lean]**:

1. `riemannHypothesis`: Mathlib's own `RiemannHypothesis`. Every zero of zeta other than -2, -4, -6, ... has real part
   1/2.
2. `riemannZeta_eq_zero_re`: the same, written out.
3. `LFunction_ne_zero_of_half_lt_re`: for every modulus N and **every** Dirichlet character chi mod N (primitive or
   not), L(chi, s) has no zero with Re s > 1/2 (the pole of the trivial character at s = 1 excepted).
4. `LFunction_eq_zero_re`: every zero of L(chi, s) in the strip 0 < Re s < 1 lies on Re s = 1/2.
5. `LFunction_eq_zero_re_of_isPrimitive`: the same for primitive characters, the usual form of GRH for Dirichlet
   L-functions.

**Scope.** "GRH" here means Dirichlet L-functions, all moduli, all characters. Dedekind zeta functions, Hecke
L-functions and automorphic L-functions in general are **not** proved (S2) **[Lean]**. The author expects the method
to extend to them, including the Extended RH, given more time (S3) **[note]**; that is **[open]**.

**Trust.** Only the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`; several
independent kernels accept the exported proof; the statement was matched against a file that imports only Mathlib
(S1, S2). The so-called literature package (`OpenLiteratureStatements`, with fields named after Caraiani's local-global
compatibility, local Langlands and Galois representations of polarized pairs) is filled by theorems proved inside the
library, and the final theorems do not depend on the local Langlands correspondence (S4 for the structure, S5 for the
dependency check) **[Lean]**, **[Lean, traced]**.

**A check that does not lean on Mathlib's zeta.** Combined with an independent formalization of Robin's and Lagarias's
criteria, the proof yields two inequalities about the divisor sum sigma(n) that mention no zeta function at all:
`robin_inequality` (sigma(n) < e^gamma n log log n for n > 5040) and `lagarias_inequality` (S2) **[Lean]**.

---

## 2. The guiding idea (the short version)

> **Count the primes the way Stepanov counted points on a curve, and let the mirror do the rest.**

The proof has two parts of very unequal size.

**The small part: the mirror.** The functional equation reflects the critical strip about the line Re s = 1/2: a zero
of L(chi, s) at s gives a zero of L(chi-bar, s) at 1 - s (for the completed L-function). So if you know there are no
zeros to the right of the line, for every character, the mirror empties the left side too, and every zero must sit on
the line. In the Lean this is `Claim.strip` and `Claim.zeta` (S4) **[Lean]**: a case split `lt_trichotomy s.re (1/2)`;
the right case is excluded by the main theorem, the left case is reflected into the right one with
`completedLFunction_one_sub` (Mathlib's functional equation), the middle case is the claim. The original release does
the same with `completedRiemannZeta_one_sub` (S4) **[Lean]**. This is the whole role of the reflection: it is the last
ten lines, not the engine. **[classical]** that this reduction works.

**The large part: a one-sided square-root count of primes.** Everything else proves one thing: for every Dirichlet
character, there are no zeros with Re s > 1/2. It gets there in three moves.

1. **A one-sided bound is enough (Landau).** Take the weighted prime sum
   G(x) = sum over n <= x of Lambda(n)(x/n - 1), minus its main term x log x - (1 + gamma) x (and its twisted
   versions for characters). If G(x) <= C x^theta on a sequence of windows [Y, Y^(1+delta)] going to infinity, there
   are no zeros to the right of theta. Only an *upper* bound is needed, because the Dirichlet coefficients of the
   combined series are made non-negative, and a Laplace transform with non-negative weights cannot hide a pole to the
   right of where it stops converging. Lean: `zeroFree_of_rpow_window`, `landau_window`, `poleData`,
   `level_of_tiedWin`, `zeroFreeAll_of_topG` **[Lean, traced]** (S5 section 1, S6 section 3). The principle is
   Landau's theorem **[classical]**; the windowed form is new in its packaging **[reading]**.

2. **Get the upper bound with exponent 1/2 from a balance (Stepanov).** Over a finite field, Stepanov proved the
   Riemann Hypothesis for curves without cohomology: build an auxiliary function that vanishes to order m at every
   rational point; it cannot vanish more than its degree allows; so (number of points) x m <= degree, and the error is
   about q/m + m, smallest at m = sqrt(q), which gives the square-root error **[classical]**. The author says the new
   argument is "a descendant of Stepanov's" (S3) **[note]**, and that over the integers the missing ingredient,
   multiplicity, is supplied by a **chain of m theta lifts** between unitary groups, with m about sqrt(X) for a prime
   sum of length X (S3) **[note]**. In the Lean the chain length is chosen as an even number near x^(1/2 - eps/16)
   (`exists_even_between`, inside the rank data `RankVal`) **[Lean, traced]** (S5 section 2, S6 section 2), and the
   error relative to the main term is about x/m + m (`proposition_size_bound`, `core_gm`) **[Lean, traced]** (S6
   section 5). The 1/2 in the final exponent is exactly the balance point of x/m against m.

3. **The "degree bound" is an arithmetic size inequality (Arakelov geometry).** Stepanov's "an auxiliary polynomial
   cannot vanish more than its degree" becomes "an arithmetic lattice cannot be more divisible than its size allows".
   One quantity is computed twice:
   - at the primes, as a sum over primes of log p times a local multiplicity, a Legendre-type count (`ASK`, built from
     `vonMangoldtClassSum`): this is the prime sum one wants to bound (Chebyshev's 1850 device of reading primes off
     factorials) **[Lean, traced]**, **[reading]** (S5 section 5);
   - at the infinite places, through periods of CM elliptic curves, which the Chowla-Selberg formula turns into the
     analytic main term with L'/L(1, chi) (`mean_log_period`, `meanPeriod`) **[Lean, traced]** (S5 section 5).

   A slope inequality (a Bost-type arithmetic Siegel lemma, `Frame_at` / `FrameF`) says the total cannot be too big,
   which yields "prime side <= main term + error" pointwise (`each_unit_bound_statement`) **[Lean, traced]**,
   **[reading]** (S5 sections 3 and 5, S6 section 6). Heights only ever give inequalities in one direction; Landau
   only needs one direction. That is why the two halves fit (S5's own summary) **[reading]**.

The remaining machinery makes step 3 honest: near-orthogonality of the lattices attached to different code words, as
if random (`LinkS`, resting on the Siegel-Weil formula, Bessel multiplicity one and a representation-theoretic
vanishing), the choice of two auxiliary primes outside a few bad moduli by a zero-density estimate, and a bound on
Tate-Shafarevich groups over large cyclotomic fields (Ferrero-Washington, Poitou-Tate, Bloch-Kato) **[Lean, traced]**
(S5 sections 6-7, S6 sections 4, 7, 8).

**In one sentence:** the proof bounds a positive-weighted prime sum from above with square-root error, by trading the
number of theta lifts (the multiplicity) against the cost of each lift, exactly as Stepanov trades vanishing order
against degree; Landau's positivity converts that one-sided bound into "no zeros right of 1/2", and the functional
equation folds the left side onto the right. **[reading]**, built on the marks above.

Why nobody saw it coming **[reading]**: Stepanov's method was always the elementary route to RH over finite fields, and
its known obstacle over the integers was that there is no notion of "vanishing to order m at a prime" with a degree to
pay for it. The proof's claim is that iterated theta lifts carry a genuine multiplicity, and that Arakelov slope
inequalities supply the degree. The author's own timeline (S3, entries 8 and 14) says the first accounting stopped at
exponent 2/3; Dixit reconstructs that 2/3 as what happens if each lift is charged for the whole chain below it
(x/m + m^2, optimum x^(2/3)), and shows the code charges each local piece to exactly one lift, which keeps x/m + m
(S6 section 9) **[reading]**. Whether that is what the author meant by 2/3 is **[open]** (S6 section 11, question 1).

---

## 3. Testing the two candidate frames

### (a) Mirror plus positivity

| Part | Fit | Evidence |
|---|---|---|
| Mirror (functional equation about Re s = 1/2) | **Fits exactly, in a small role.** It is the last step and does no work against the zeros. | `Claim.strip`, `Claim.zeta`, `Claim.prim_reflect` use `completedLFunction_one_sub` (S4) **[Lean]**. |
| Positivity | **Fits, but not Weil's positivity.** The engine is one-sided inequalities: non-negative Dirichlet coefficients for Landau, and positivity of arithmetic heights and slopes. | `poleData` gives residues that are positive multiples of one number, so no cancellation (S5 section 1); the levels used weight characters so every coefficient is at least a positive multiple of Lambda(n) (S6 remark 6) **[Lean, traced]**. |
| Mirror and positivity joined (Weil's criterion: positivity of the explicit-formula pairing of f with its reflected conjugate) | **Does not fit the final proof.** No statement of the form "the Weil functional is non-negative on all convolution squares" is on the path. The two ingredients appear separately. | The note's timeline mentions W(...) >= 0 steps and credits Guinand-Weil with the right sign (S3, entries 4-6) **[note]**, but the traced final path ends in the windowed Landau argument, not in Weil's criterion (S5 section 1, S6 section 3) **[Lean, traced]**. Whether those timeline steps survive inside the lattice layer in another form is **[open]**. |
| Reflection positivity in the OS sense (a positive pairing built from a reflection) | **Does not fit.** Positivity here comes from heights and coefficients, never from a reflected pairing. | No such pairing found on the traced path (S5, S6) **[reading]**. |

**Verdict:** partial. Mirror yes, positivity yes, but they are two separate tools; the thing that makes positivity bite
is a Stepanov balance, not a reflection.

### (b) Hilbert-Polya (zeros as the spectrum of a self-adjoint operator)

**Does not fit.** No operator whose eigenvalues are the zeros is constructed. Spectral theory is everywhere, but as a
tool: discrete series of unitary groups, formal degrees, Schur orthogonality and a pre-trace-formula shape are used to
prove that the subspaces attached to different code words are nearly orthogonal (`LinkS`, with
`theoremS_transport_link_zero`, `SiegelWeilUnitaryConvergent`, Bessel multiplicity one) **[Lean, traced]** (S5
section 7). The note says a variance trick gives things the look of a trace formula and lists a relative trace formula
(S3, entries 5 and 16) **[note]**; neither turns the zeros into a spectrum. No file name in the library mentions
Hilbert-Polya (S4, partial path list) **[Lean]** for the search, **[reading]** for the conclusion.

### (c) The frame that fits: Stepanov transplanted

Stated by the author (S3) **[note]**, visible in the code as the m-versus-x/m balance (S6) **[Lean, traced]**. This is
the frame section 2 uses.

---

## 4. The skeleton, stage by stage

Top-down, as the final theorem actually uses it. Names in `code`.

| Stage | What it does | Key Lean names | Classical ingredients | Mark |
|---|---|---|---|---|
| 0. Fold | No zeros right of 1/2 for all chi, plus the functional equation, gives all zeros on the line; zeta is the trivial character mod 1. | `Claim.strip`, `Claim.zeta`, `Claim.prim_reflect`, `Claim.prim_zero`, `Claim.factor_ne_zero`; original: `UpperTheory.riemannHypothesis_of_everyCharacter` | functional equation, Euler product (extra Euler factors have no zeros for Re s > 0) | [Lean] |
| 1. Entry | `UpperTheory.EveryCharacter` (= theorem 3) from the literature package and `VWin`. | `UpperTheory.FinalTheorems.everyCharacter`, `every_character_of_literature_of_vWin`, `every_character_of_theta_integrals_local_matching` | (bookkeeping) | [Lean] for the first two; [Lean, traced] below |
| A. Windowed Landau | A one-sided bound G <= C y^theta on windows rules out zeros right of theta. | `zeroFree_of_rpow_window`, `landau_window`, `poleData`, `landau_coeff`, `level_of_tiedWin`, `zeroFreeAll_of_topG` | Landau's theorem (non-negative coefficients), Taylor-coefficient proof | [Lean, traced] |
| B. Isolating chi | Fourier averaging over a small group picks out the target character; two auxiliary primes q = 3 mod 8, d = 7 mod 16 are chosen so their characters are harmless. Their L-functions are **not** proved to satisfy GRH; bad moduli are avoided. | `ch_balance`, `GrowthInequalityExplicit`, `QH.pairEx`, `count_bad_core`, `ZD.zero_density_box` | zero-density estimates, large sieve, mollifiers | [Lean, traced] |
| C. Size balance | Error relative to main term about x/m + m; m about sqrt(x). | `core_gm`, `proposition_size_bound`, `RankVal`, `exists_even_between` | Stepanov's balance | [Lean, traced]; [note] for the Stepanov link |
| D. Divisibility / slopes | Prime side `ASK` vs archimedean side `MAIN`; slope inequality gives ASK <= MAIN + Err for every point; chain of m lifts as submultiplicative norms. | `Frame_at`, `FrameF`, `each_unit_bound_statement`, `key_identity5`, `height_chain_atR`, `mean_log_period`, `meanPeriod` | Arakelov slopes (Bost), arithmetic Siegel lemma, Legendre's formula, Chowla-Selberg, Kronecker limit formula | [Lean, traced]; [reading] for "Bost-type" |
| E. Near-orthogonality | Code subspaces nearly orthogonal (error e^(-x^(eps/8))). | `LinkS`, `theoremS_transport_link_zero`, `SiegelWeilUnitaryConvergent`, `kernel_diagonal_positive` | Siegel-Weil formula, Schur orthogonality, discrete series, Bessel multiplicity one, theta correspondence (Rallis, seesaw) | [Lean, traced] |
| F. Tate-Shafarevich window | Bounds on Sha of cyclotomic fields of degree about x^2. | `VWin`, `vwin_of_row`, `Row0b`, `galoisLocalGlobalStrong_recParameter`, `UpperTheory.V.FW.ferreroWashington` | Ferrero-Washington (mu = 0), Poitou-Tate, Bloch-Kato, Galois representations via theta lifts | [Lean, traced] |

Parameters, for orientation (S6 section 2) **[Lean, traced]**: eps < 1/52; m about x^(1/2); the host has about x^2
characters; the word length k about x^(9/2); a common weight b = exp(x^eps) that swamps every polynomial loss. The
lifts walk the signature of a unitary group from (k-1, m) to the definite (k+m-1, 0), one step per lift (S6 section 2)
**[Lean, traced]**; the note speaks of lifts between totally definite unitary groups (S3, entry 8) **[note]**.

What the code does **not** contain on the final path, per the exact dependency lists (S5): the all-scales Landau
theorem `landau_family`, an averaged mean bound, and several duplicate routes **[Lean, traced]**. About twenty unused
variants of the growth bound exist, all ending at exponent 1/2 + O(eps); none at 2/3 (S6 section 9.4)
**[Lean, traced]**.

---

## 5. Where it meets what was presumed true

Legend: **confirmed** = the proof establishes it (as a Lean theorem or an immediate special case); **follows** = a
classical consequence of the proved GRH, not formalized here; **used** = an input to the proof; **bypassed** = a known
route to RH that the proof does not take; **unrelated** = the proof neither uses nor touches it.

| Classical expectation | Status | Evidence |
|---|---|---|
| RH for zeta | **confirmed** | `riemannHypothesis` (S2) [Lean] |
| GRH for Dirichlet L-functions | **confirmed** | theorems 3-5 (S2) [Lean] |
| GRH for Dedekind, Hecke, automorphic L-functions; Extended RH | **open** | not among the checked statements (S2); author expects it (S3) [note] |
| No Siegel (exceptional real) zeros | **confirmed** as a special case | theorem 3 excludes every real zero in (1/2, 1) for every character (S2) [Lean]; [classical] that this is the Siegel-zero question |
| Functional equation (the mirror) | **used**, in the last step only | `completedLFunction_one_sub` in `Claim.prim_reflect` (S4) [Lean] |
| RH equivalent to psi(x) = x + O(x^(1/2+eps)) | **used** in one-sided, windowed form; it is the heart | `Gz`, `zeroFree_of_rpow_window` (S5, S6) [Lean, traced]; equivalence [classical] |
| Landau's theorem (non-negative coefficients) | **used** (windowed version) | `landau_window`, `poleData` (S5 section 1) [Lean, traced] |
| Explicit formula (Riemann-von Mangoldt, Guinand-Weil) | **used** as a tool; the final step is Landau's pole argument, which carries the same Mellin-transform content | a truncated explicit formula over zeros right of 1/2 is proved (`explicit_formula_dirichlet_zeros_right_half`) [Lean]; whether it is on the final path I did not check [open]; the timeline credits Guinand-Weil with the sign (S3 entry 5) [note] |
| Weil's positivity criterion | **bypassed** on the final path | traced endgame is Landau (S5, S6) [Lean, traced]; W(...) >= 0 steps only in the timeline (S3 entries 4, 6) [note] |
| Hilbert-Polya (zeros = spectrum of a self-adjoint operator) | **bypassed** | no such operator; spectral theory used for near-orthogonality only (S5 section 7) [Lean, traced] |
| Montgomery-Dyson pair correlation / GUE statistics | **unrelated** | the proof says nothing about spacing of zeros on the line [reading]; GUE remains a conjecture [open] |
| de Branges spaces; Connes-type trace formula approaches | **bypassed** | no file name mentions de Branges; no such structure in the traced path (S4, S5) [reading] |
| Li's criterion (lambda_n >= 0) | **follows** (equivalent to RH), not formalized | [classical]; not among the stated theorems (S2) |
| Robin's and Lagarias's criteria | **confirmed** and formalized | `robin_inequality`, `lagarias_inequality` (S2) [Lean] |
| Lindeloef hypothesis | **follows**, not formalized | [classical]; a Phragmen-Lindeloef convexity bound appears as a tool (file `NormCompletedHeckeLCMOneLePhragmenLindelof`) (S4) [Lean] for the file name only |
| Primes in progressions with square-root error (GRH-level) | **follows**, not formalized | [classical] |
| Zero-density estimates | **used** (to choose auxiliary moduli) | `ZD.zero_density_box`, `logFree_zeroDensity_dirichlet_one_modulus` (S4, S5, S6) [Lean] for the statement, [Lean, traced] for the role |
| Classical zero-free regions | **used** (boxes Re s > 1 - 1/400 for auxiliary characters) | `HostGood`, `BoxW` (S5 section 7) [Lean, traced] |
| RH over finite fields (Weil; Deligne); Stepanov's elementary proof | **used as the model**, not as an input | the note calls the argument a descendant of Stepanov's (S3) [note]; balance x/m + m in code (S6) [Lean, traced]; the note also mentions a proof of Weil's and Deligne's bounds using only a sign, from the author's earlier work (S3) [note] |
| Siegel-Weil formula; theta correspondence (Howe, Rallis, seesaw) | **used** | `SiegelWeilUnitaryConvergent`, `RallisDM` import, seesaw in the timeline (S3 entry 12, S4, S5) [Lean, traced] |
| Chowla-Selberg formula; Kronecker limit formula | **used** | `mean_log_period`, `chowla_selberg_period` (S5 section 5) [Lean, traced] |
| Arakelov slope inequalities (Bost), arithmetic Siegel lemma | **used** | `Frame_at` (S5 section 3) [Lean, traced]; a Bost slope inequality in the timeline (S3 entry 13) [note] |
| Iwasawa theory: Ferrero-Washington, Poitou-Tate, Bloch-Kato | **used** | `ferreroWashington`, Sha window (S6 section 8) [Lean, traced] |
| Local Langlands correspondence | **bypassed** (only a weaker local statement `RecTExists` is used) | S5 section 7 item 3 [Lean, traced] |
| GRH for the auxiliary characters | **not assumed**; avoided by choice of moduli | S6 remark 16 [Lean, traced] |

**Headline of the table:** the proof confirms RH and Dirichlet GRH (and with them the Robin and Lagarias inequalities and
the absence of Siegel zeros), uses the old prime-counting equivalence and Landau's positivity as its spine, and bypasses
the three famous structural programmes (Weil positivity, Hilbert-Polya, random-matrix statistics). Its real model is
the elementary function-field proof of Stepanov, rebuilt with theta lifts and Arakelov geometry.

---

## 6. What remains open or unverified

- No human-written proof exists yet; the author plans one and expects large simplifications (S3) **[note]**.
- The semantics of some formalized "published" statements against the literature is still being audited; a mismatch
  would not affect validity, only labels (S5 section 7 item 3) **[open]**.
- Several deep proofs (Siegel densities, Bessel multiplicity one, the off-diagonal bound `CarrierGap.offDiag`) are
  kernel-checked but not yet read by humans (S5 section 7) **[open]**.
- The source of the author's 2/3 barrier (S6 section 11) **[open]**.
- Whether the Weil-positivity steps in the timeline (S3 entries 4-6) live on inside the lattice layer **[open]**.

---

## 7. DMP readings (separate; not mathematics)

> **This section maps the owner's DMP readings (from `docs/mass-gap/weak-coupling/PREP.md`, S8) onto the proof's
> skeleton. Nothing here is a mathematical result. Each item is marked exact correspondence / analogy / does not fit,
> and the mathematical facts it leans on carry their own marks.**

**D1. Duality as the mirror.** Reading (S8): the functional equation is a duality s <-> 1 - s, and the completed
xi(s) = xi(1 - s), with the real place (Gamma factor) included, is the object to study.
- **Exact correspondence** for what the Lean does in stage 0: it works with the *completed* L-function
  (`completedLFunction`, `completedRiemannZeta`) precisely because only the completed one is symmetric; the Gamma
  factor is divided out with `gamma_ne_zero` (S4) **[Lean]**. So "the duality only closes once the real place is
  included" is literally the shape of `Claim.prim_reflect`.
- **Does not fit** as a claim about where the proof's force comes from: the duality is the last fold, and the hard
  part (stages A to F) never uses it. A DMP reading that "duality proves RH" would misdescribe this proof.

**D2. The half-line as the duality's axis.** Reading (S8): Re s = 1/2 is the fixed line of the mirror; the owner's
"inversion and halving".
- **Exact correspondence** (mathematical fact, **[classical]**): Re s = 1/2 is the fixed line of s -> 1 - s-bar.
- **A second 1/2, worth noting.** In this proof the line also appears independently, as the balance point of the
  multiplicity trade-off: error about x/m + m, smallest when m = x/m, i.e. m = sqrt(x), giving exponent 1/2, which
  Landau turns into "no zeros right of Re s = 1/2" (S6) **[Lean, traced]**. The two halves (mirror axis and
  balance point) come from different places and meet only in the conclusion. The owner's "inversion and halving"
  maps onto the balance well: *inversion* is m against x/m (each the other's reciprocal partner at fixed x), *halving*
  is taking the geometric mean, the exponent 1/2. **Analogy**, but a close one: the arithmetic is exact, the DMP
  wording is a description of it.
- That the mirror's axis and the balance point coincide is not explained by the proof; it is what RH asserts.
  Any DMP claim that they "must" coincide for a common reason is **[open]** and not a result.

**D3. The reals as two-sided cuts.** Reading (S8): a real number is a Dedekind cut, a split into a lower and an upper
side, "binary like a boundary".
- **Exact correspondence in logical form.** The final step is a three-way split of Re s at the cut 1/2:
  `lt_trichotomy s.re (1/2)` in `Claim.strip` (S4) **[Lean]**. The upper side is emptied by the Stepanov-Landau engine,
  the lower side by the mirror, and what is left is the cut itself. The author's footnote reports that the generated
  write-up begins exactly with this trichotomy of the reals at 1/2 (S3, footnote 2) **[note]**.
- **Caveat:** trichotomy is the order of the reals and is used in countless proofs; the correspondence describes the
  proof's last step, it adds no content to it. **Analogy** for any stronger reading.

**D4. Binary existence and binary words.** The lattices are indexed by binary code words of length about k - 2
(`exists_injective_words`, `Win_at` requires log #W <= (k - 3) log 2) (S5 section 2, S6 section 5.2)
**[Lean, traced]**. **Does not fit** the binary-existence reading: the words are a counting device whose only cost is
the pigeonhole term log #W; they carry no two-sided or reflected structure. Recorded so the coincidence of the word
"binary" is not mistaken for a link.

**D5. Reflection positivity / OS reconstruction <-> Weil positivity; Hamiltonian <-> Hilbert-Polya.** Reading (S8 and
the brief): the Yang-Mills proof's reflection positivity (a positive pairing gives a Hilbert space and a self-adjoint
Hamiltonian) may parallel Weil positivity and Hilbert-Polya.
- **Does not fit this proof** (section 3): neither Weil's criterion nor a Hilbert-Polya operator is used.
- **A parallel that does fit, at the level of a shared lemma (analogy, with a classical core).** The proof's stage A is
  Landau's principle: a Laplace transform of non-negative weights has its first singularity where convergence stops,
  so a one-sided growth bound pushes every singularity to the left of the bound's exponent **[classical]**. The mass
  gap side has the same lemma in another dress: with reflection positivity, a correlation function is the Laplace
  transform of a positive spectral measure, so its exponential decay rate equals the bottom of the spectrum above the
  vacuum, the gap **[classical]** (OS reconstruction, spectral representation). In both, positivity of the weights is
  what lets a one-sided bound speak about where the singularities (zeros there, spectrum here) can be. **Analogy**:
  the shared mathematics is the Pringsheim-Landau theorem; the identification of zeta zeros with any physical spectrum
  is not made by this proof and is **[open]**.

**D6. zeta(-1) = -1/12.** Reading (S8): -1/12 as the term binary existence requires. **Unrelated to this proof**: RH and
GRH concern the zeros, and the value at -1 (Euler; reflected from zeta(2) = pi^2/6 by the same functional equation,
**[classical]**) plays no role in the Lean argument (S4, S5, S6) **[reading]**. The only shared object is the
functional equation of D1.

**Summary of the DMP mapping:** two exact correspondences of form (the completed mirror in stage 0; the cut at 1/2 in
`Claim.strip`), one close analogy with exact arithmetic behind it (inversion and halving as the m <-> x/m balance at
sqrt(x)), one sound analogy across the two projects (positivity plus a one-sided bound locates singularities: Landau
here, spectral gap there), and three readings that do not fit this proof (duality as the engine, binary words,
Weil/Hilbert-Polya as the route).
