# Part IV. The generalised Riemann hypothesis: the positivity route

*Draft 6. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/ProofPhase/`; notes relative to
`docs/rh-guide/`. Claim labels (IV.n) are listed in `../CLAIMS.md`.*

**Plug in here.** Gives: the positivity route to GRH, the explicit formula and the first certified box. Needs: II.4.1, and
II.2.7 for the turn. Route: the exact route, stop 4. VIBE coefficient: here v is the paper's own a. Up to a = log 4 / 2 = log 2 only
the real place and the primes 2 and 3 enter, and Weil's form is certified positive at a = 0.60, 0.65 and 0.69 (IV.1)
**[certified]**; beyond it lies the open step. R.12o, v's abstract statement, reads this positivity, measured through zeta, as
what v certifies **[reading]**; by Weil's criterion one negative value would refute RH (II.9.4) **[classical]**.

**As a statement checked step by step (II.4.1).** For a finite zero model the statement is the sign at every scale (`ScaleSign`),
and the card's box checks it at every step (`grh_box_iff`, IV.8) **[Lean]**. The statement is the same at every step, so the
inductive step is free and the open part is the base case, the whole of `ScaleSign`. The certified first scales (IV.1, the first box)
are progress inside that statement, not part of the induction.

## IV.0 What is proved, by whom, and what this part does

**State of the problem.**

* The Riemann hypothesis for zeta and GRH for every Dirichlet L-function are proved in Lean by others: a library released
  2026-11-20; the Riemann hypothesis was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and the Dirichlet
  theorems are checked on the library's verification page **[external]** (`SOURCES.md`, S1 to S4; `GUIDE.md`,
  section 1). This project read the main statements in the source and did not rebuild the library.
* GRH for Dedekind, Hecke and general automorphic L-functions is not proved **[open]** (`GUIDE.md`, sections 1 and 5).
* As far as this project traced it, the proof by others does not go through Weil's positivity criterion (the positive pairing of
  II.8). Positivity enters it elsewhere: its sign is the non-negative coefficients of Landau's theorem (IV.2.3, IV.2.4). Its endgame,
  as traced here, is Landau's theorem applied to a one-sided square-root bound on the prime count, obtained from a Stepanov-type
  size balance **[external, traced, preliminary]** (`GUIDE.md`, sections 2, 4, 5).
* Tao's post of 20 November 2026 (Tao 2026) reports that L. Alpoge, the author of that library's proof, has also generated a Lean-only proof of a Generalized
  Riemann Hypothesis and, as a preliminary analysis, that its strategy appears to use the full power of modern developments in the
  Langlands program. Which L-functions that proof covers is not stated there, and how its route relates to the one traced above was
  not examined here **[external, unverified]**.

**What this part does.** It follows the other road: Weil's positivity criterion, the second column of the chain of II.8. It proves the
chain in finite models (IV.1), shows exactly why a mirror symmetry alone cannot place zeros on the line (IV.2), measures the shape of
the missing positivity (IV.3), and states the one missing construction in eight faces (IV.4), with "it runs" as the
form shared with Yang-Mills (IV.5). **This part does not prove GRH for any L-function.** Its value is a reduction that is independent of
the existing proof and would, if closed, extend to L-functions the existing proof does not reach.

## IV.1 The chain in finite models (links 1 to 4)

In a finite model everything works: zeros are finitely many, the pairing is a finite sum, and "positive" means "on the line".

| # | Result | Status | Source |
|---|---|---|---|
| II.9.3 | Finite Weil criterion: zeros closed under conjugation; the zero pairing is non-negative on every finite exponential sum iff every zero is on the line | **[Lean]** | `GRH/Weil.lean`, `weil_criterion_finite` |
| IV.1.2 | Zeros on the line imply the pairing is non-negative (each term is a square) | **[Lean]** | `GRH/Weil.lean`, `weilSum_re_nonneg_of_real` |
| IV.1.3 | Positivity implies the line for any test class with the approximation property and finite multiplicities (named hypotheses) | **[Lean]** | `GRH/Weil.lean`, `real_of_weilSum_nonneg` |
| II.9.4 | Weil's criterion for zeta and Dirichlet L-functions | **[classical]** | Weil 1952; Bombieri 2000 |
| IV.1.5 | Weil's explicit formula for zeta holds for every smooth compactly supported test function, by the contour shift, with a polynomial zero count per unit window (Mathlib-only core, no named step); the real-place term is a line integral at Re s = c > 1, and its identification with the term of Weil's closed form on the critical line is not in Lean | **[Lean]** | `GRH/ContourShift.lean` (`CS.contourShift`), `GRH/ContourShiftTie.lean` (`explicit_formula_of_smooth`), `GRH/ContourShiftZeta.lean` (`zero_count_window`) |
| IV.1.5b | For Dirichlet and other L-functions the explicit formula, and Weil's criterion itself, are classical but not yet in Lean | **[classical]** (not in Lean) | `docs/unified/CONTOUR-SHIFT.md`, section 5 |
| IV.1.6 | A similitude multiplying a positive form by q has all eigenvalues of modulus sqrt q | **[Lean]** | `GRH/Orbits.lean`, `similitude_eigenvalue` |
| IV.1.7 | If Theta - 1/2 is skew-adjoint for a positive form, every eigenvalue has real part 1/2 (finite dimension) | **[Lean]** | `GRH/Orbits.lean`, `skew_shift_re_half` |
| IV.1.8 | Lee-Yang circle theorem and Asano contraction, small cases | **[Lean]** | `GRH/LeeYang.lean`, `asano`, `ising3_zeros_on_circle` |
| IV.1.9 | Fixed points of f^n are counted by points of exact period d dividing n (finite "remnants as evidence") | **[Lean]** | `GRH/Orbits.lean`, `card_fixed_pow_eq_sum` |
| IV.1.10 | A finite exponential sum bounded by any exponential constant is bounded exactly ("a lossy bound becomes exact on a finite spectrum") | **[Lean]** | `GRH/Induction.lean`, `norm_le_of_exp_bound` |

**The explicit formula, as proved (IV.1.5).** Let c > 1, let g : R -> C be smooth with compact support, and let (gamma_i) list the
nontrivial zeros rho = 1/2 + i gamma_i of zeta with multiplicity. Write $H(s) = \int g(x)\, e^{(s - 1/2)x}\, dx$ and $\tilde g(x) = g(-x)$.
Then the sum over i of $H(\tfrac12 + i\gamma_i)$ converges, and

$$\sum_i H(\tfrac12 + i\gamma_i) = H(1) + H(0) - \sum_{n \ge 2} \frac{\Lambda(n)}{\sqrt n}\bigl(g(\log n) + g(-\log n)\bigr) + \tfrac12\bigl(A_c(g) + A_c(\tilde g)\bigr),$$

where $A_c$ is the real-place term, a line integral at Re s = c of the digamma factor against the transform of g **[Lean]**
(`GRH/ContourShiftTie.lean`, `explicit_formula_of_smooth`; `GRH/ExplicitFormula.lean`, `efRHS`). The formula is Weil's
**[classical]**; what is new is the formalisation, with no named step. That $A_c$ equals the real-place term of Weil's closed form
on the critical line is not in Lean.

**The explicit formula is one turn (IV.1.5c).** The contour shift moves the line integral of H(s) times the logarithmic derivative
Lambda'(s)/Lambda(s) of the completed zeta function from Re s = c to Re s = 1 - c, and the difference of the two lines is an integral
once around the critical strip. Each zero contributes its order times H at the zero, and the order is the winding number of one turn
of the logarithmic derivative around it (II.2.7, `full_turn_order`); the poles at s = 0 and s = 1 wind -1 each and give the terms
H(0) + H(1) **[Lean]** for the local winding at a zero, **[paper]** for reading the formula as the full turn taken once around the strip
(claim IV.1.5c).

**The certified first box, as stated.** For a = 3/5, 13/20 and 69/100 and every f in L^2(-a, a), real or complex,

$$c(a)\,\|f\|^2 \le W(f), \qquad c(\tfrac35) = 1.500\cdot 10^{-9},\quad c(\tfrac{13}{20}) = 3.398\cdot 10^{-11},\quad c(\tfrac{69}{100}) = 6.417\cdot 10^{-13},$$

where W is Weil's quadratic form of zeta on test functions supported in [-a, a]: the real place, with the constant
$-\log\pi - \gamma - \log 4a$, and the prime powers n with log n < 2a, here only 2 and 3, with weights $\Lambda(n)/\sqrt n$. The three
numbers are enclosed in ball arithmetic (`docs/unified/grh_onebox_cert-a0.60.log`, `-a0.65.log`, `-a0.69.log`; rerun with
`tools/reproduce.sh certs`) **[certified]**; the analytic estimates that make them bounds on all of L^2(-a, a) (a polynomial part
of degree below 100, a tail, and the cross term between them) are argued in `docs/unified/GRH-ONEBOX-CERT.md` **[paper]**, and the
assembly from the three inputs is **[Lean]** (`GRH/OneBoxCert.lean`, `onebox_positive`) (claim X.65).

## IV.4 The open step: one missing positivity, eight faces

The missing piece: **a positive object built from the primes, the characters and the real place alone, without the zeros.** For
zeta and the Dirichlet L-functions the positivity itself now follows from the external theorem and Weil's criterion (II.9); what
stays open there is a proof from arithmetic alone, and beyond Dirichlet the statement itself, for which no card is written yet
(IV.1.5b). The step asks for non-negativity at every support, not for a margin uniform in the support, which is false for zeta's
zero measure (X.45b). The notes have met it eight times. Each face, if built, would give the open step; the relations proved among the faces are the two
stated below the table.

| Face | Statement | Status | Source |
|---|---|---|---|
| 1 Weil Hilbert space | A Hilbert space H_chi and a map Phi from test functions, built from arithmetic data only, with <Phi f, Phi g> = W_chi(f * g~). By Weil and GNS it exists iff GRH holds for chi. None of its subset truncations is positive (IV.3.5) | **[open]** | `grh/ATTEMPT.md`, step 4 |
| 2 Critical ferromagnet | A lattice ferromagnet at its critical coupling whose block-spin law is Riemann's Phi; RH by Newman's closure. Asano adds one site at a time; here one prime at a time fails | **[open]** | `grh/LEE-YANG.md`, 5c |
| 3 Deninger space | A foliated space whose closed orbits are the primes, with a positive leafwise Hodge form. In the hyperbolic analogue positivity gives only "line or real segment"; the line needs a gap (lambda_1 >= 1/4) | **[open]** | `grh/ORBITS.md`, 6; `grh/TRANSFER.md`, 5 |
| 4 Hermite-Biehler chain | A Hermite-Biehler coupling of xi's real and imaginary parts (de Branges frame; Conrey and Li 2000 examine de Branges' positivity conditions and indicate their difficulty; that a stated condition fails is recalled, not checked here); its Schur parameters are the step factors | **[open]**; framework **[classical]** | `grh/INDUCTION.md`, 0.4 |
| 5 Step lemma | From the primes up to p_{k+1} and the real place, put the new corner entry inside the extrapolated interval, without the zeros | **[open]** | `grh/INDUCTION.md`, 7 |
| 6 Sign of the remnant | From arithmetic alone, lambda_min(a) >= 0 at every support; equivalently the ground states converge to the zero measure | **[open]** | `grh/VARIATIONAL.md`, 0.5 |
| 7 Global sign ("it runs") | The norm in which the scaling flow runs is positive; equivalently the one-sided square-root prime bound. In the constructions where the norm is positive by construction, the space either misses the off-line zeros (Connes) or yields a half-plane (Lax-Phillips) (recalled, not traced to a page) | **[open]** | `grh/TATE.md`, 0.5, 0.6 |
| 8 All-or-nothing step | At each scale the full set of primes present, and no subset, places the corner entry inside the interval; no decomposition into pairs, single primes or two terms carries it | **[open]** | `grh/TRANSFER.md`, 5 |

Faces 2 and 3 each imply face 1 **[paper]** (`grh/INDUCTION.md`, 7; `grh/ORBITS.md`, 4). Faces 5, 6 and 8 are the same quantity read
between scales, at one scale, and over subsets **[paper]** (`grh/VARIATIONAL.md`, 5; `grh/TRANSFER.md`, 5).

**The constraint on any construction** (IV.3): it cannot add one prime at a time with slack; it cannot assemble positivity place by
place or subset by subset; it cannot separate the archimedean part from the primes. All primes up to the scale and the real place must
enter together, in their exact relative position, through an exact identity.

**The full text.** This part is contracted. Every derivation it leaves out is in the full Draft 6 at the git tag `d6-full`, and in Draft 5 section by section; every claim keeps its row, status and evidence in `../CLAIMS.md`.
