# The explicit formula for zeta in Lean: "toy = not-toy", reduced to one named step

Status: 2026-11-23. Follows `GRH-TIE-IN.md` (sections 0, 2.2, audit item 10) and `TRANSPORT.md` 3.2. Under the construction
principle: content from the best existing results, cited and audited; the project supplies the tying theorems.

Files:
- Lean (`docs/mass-gap/formal/ProofPhase/GRH/`): `ExplicitFormulaPrime.lean` (layer a), `ExplicitFormula.lean` (layer b),
  `ExplicitFormulaTie.lean` (layer c). `explicitformula-axioms.sh` and `explicitformula-axioms.log`: 64 declarations, all
  on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), no `sorry`, no `native_decide`, no warnings in
  the three files. Build target `ProofPhase.GRH.ExplicitFormulaTie`.
- Numerical check: `explicit_formula_check.py`, `explicit_formula_check.log`. CPU only, about a minute, mpmath.

Status marks as in `OPEN-STEPS-DMP.md`: **Lean**, **classical**, **external**, **numerical**, **reading**, **open**.

---

## 0. In plain words

**What the explicit formula is.** It is the exact equation between primes and zeros. Take a test function `g` on the
log scale (a smooth bump), and its transform `H`. Then

> sum of `H` over all nontrivial zeros of zeta
> = `H(1) + H(0)` (the pole terms)
> - sum over prime powers of `Lambda(n) n^{-1/2} (g(log n) + g(-log n))` (the prime side)
> + an integral of `H` against the digamma function (the real place).

The project's GRH ledger uses this equation without saying so: its "prime-side moments" are the right side, and Weil's
zero pairing is the left side. `TieIn.lean` named it as a hypothesis, `ExplicitFormula`. The owner calls it
"toy = not-toy". Mathlib does not have it.

**What was done.** The equation is now in Lean, proved from one precisely stated classical step, the **contour shift**
(`ContourShift`). Everything around that step is a theorem:
- the prime side is a theorem: `-zeta'/zeta = L(Lambda, s)` on a vertical line `Re s = c > 1`, integrated against the
  transform of the test function, is exactly the prime sum `sum Lambda(n) n^{-1/2} g(log n)` (Fourier inversion and an
  exchange of sum and integral, both proved);
- the real place is a theorem: the Gamma factor of the completed zeta contributes `(psi(s/2) - log pi)/2`;
- the functional equation is used as a theorem: the line `1 - c` turns into the line `c` with the mirrored test function;
- the assembly is a theorem: given the contour shift, the explicit formula follows in the standard form;
- the tie is a theorem: for smoothed grid cells, the explicit formula gives `TieIn`'s `ExplicitFormula` hypothesis by
  bilinearity, so the zeta column of the ledger runs from `ExtRH` and `ContourShift` to `ScaleSign`.

**What the named step is.** The contour shift says: the difference of the two vertical line integrals of
`-Lambda'/Lambda * H` (at `Re s = c` and `Re s = 1 - c`) is the sum of the residues between them, with the zero sum
converging absolutely. It is the residue theorem on rectangles of growing height plus the estimates that make the top and
bottom sides vanish. Classical (Weil 1952; Iwaniec-Kowalski, *Analytic Number Theory*, Thm 5.12; Davenport, ch. 17).
Mathlib lacks the three things it needs: the residue theorem on rectangles, the zero count of zeta, and the bound on
`zeta'/zeta` near the zeros. Section 5 says what it would take.

**Checked numerically.** With 200 zeros and four shifted Gaussian test functions, the formula in exactly the Lean
normalisation holds to 30 digits, and a control with the prime sign flipped fails by about 1. So the named step is
stated with the right signs and normalisation (a wrong sign would have made it false and the tie vacuous).

**What this does not do.** It does not prove RH or GRH. The sign of the ledger still comes from the external RH proof
(`ExtRH`) through the easy direction. It covers zeta, not yet Dirichlet L-functions (section 6). The analytic heart, the
contour shift, is named, not proved.

---

## 1. The layer plan

| layer | content | file | status |
|---|---|---|---|
| (a) | prime side as a line integral; log-derivative of the completed zeta; real place (digamma); functional equation of `Lambda'/Lambda` | `ExplicitFormulaPrime.lean` | **Lean** |
| (b) | Weil's explicit formula for zeta, test class `EFTest`, from the named `ContourShift` | `ExplicitFormula.lean` | **Lean**, one named classical input |
| (c) | `TieIn`'s `ExplicitFormula` for smoothed cells, and the zeta column of the ledger | `ExplicitFormulaTie.lean` | **Lean**, same named input |
| (d) | the contour shift itself | (not started) | **classical**, named; section 5 |

## 2. Layer (a): the prime side and the real place [Lean]

What Mathlib v4.34.0 has and was used: `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (`L(Lambda, s) = -zeta'/zeta` for
`Re s > 1`), `riemannZeta_def_of_ne_zero` and `Gammaℝ_def` (`Lambda(s) = pi^{-s/2} Gamma(s/2) zeta(s)`),
`completedRiemannZeta_one_sub`, `riemannZeta_ne_zero_of_one_le_re`, `digamma`, Fourier inversion
(`Integrable.fourierInv_fourier_eq`), and `integral_tsum_of_summable_integral_norm`.

Conventions. The vertical line is parametrised as `s(tau) = c - 2 pi i tau` (`vpt`), so that
`integral f(s(tau)) dtau = (1/2 pi i) integral_{(c)} f(s) ds` (`vline`) and the transform of the test function on that
line is Mathlib's Fourier transform of the tilted function `g(x) e^{(c - 1/2) x}` (`tilt`, `laplace_vpt`).

| declaration | says |
|---|---|
| `neg_logDeriv_zeta` | `-zeta'/zeta = L(Lambda, s)` for `Re s > 1` |
| `logDeriv_Gammaℝ` | `Gamma_R'/Gamma_R (s) = -(log pi)/2 + psi(s/2)/2` for `Re s > 0` |
| `logDeriv_completedZeta` | `Lambda'/Lambda = zeta'/zeta + Gamma_R'/Gamma_R` for `Re s > 1` |
| `logDeriv_completedZeta_one_sub` | `Lambda'/Lambda (1 - s) = -Lambda'/Lambda (s)` for `s != 0, 1` |
| `term_vM_vpt`, `LSeries_vM_vpt`, `continuous_LSeries_vM_vpt`, `norm_LSeries_vM_vpt_le` | `L(Lambda, .)` on the line `c > 1`: a uniformly convergent sum of phases, continuous, bounded by `sum Lambda(n) n^{-c}` |
| **`lineIntegral_LSeries_vonMangoldt`** | `integral L(Lambda, c - 2 pi i tau) F[phi](tau) dtau = sum_n Lambda(n) n^{-c} phi(log n)` for `phi` continuous, integrable, with integrable Fourier transform |
| **`lineIntegral_primeSide`** | the same with `phi = g e^{(c-1/2)x}`, `g` continuous with compact support: the right side is `sum_n Lambda(n) n^{-1/2} g(log n)`, independent of `c` |

## 3. Layer (b): Weil's explicit formula from the contour shift [Lean + one named input]

**Test functions.** `g : R -> C` continuous with compact support; `H(s) = integral g(x) e^{(s - 1/2) x} dx` (`laplace`). On
the critical line `H(1/2 + i z) = integral g(x) e^{i z x} dx` (`laplace_half`), the transform the ledger uses. The test
class on the line `c`, `EFTest c g`, adds two integrability conditions: the transform on the line, and the transform times
`Gamma_R'/Gamma_R`, are integrable. Classically both hold for `g` twice continuously differentiable with compact support
(two integrations by parts give `H(c + it) = O(1/t^2)`, and `Gamma_R'/Gamma_R = O(log t)`); **not formalised**: in Lean
the class is shown nonempty only by `g = 0` (`efTest_zero`).

**The named input.**
- `ResidueShift c g rho`: the family `rho` is summable against `H`, and
  `vline(-Lambda'/Lambda * H, c) - vline(-Lambda'/Lambda * H, 1 - c) = H(1) + H(0) - sum_i H(rho_i)`.
  The residues: `+H(1)` and `+H(0)` from the simple poles of `Lambda` at `1` and `0`; `-m H(rho)` at a zero of order `m`.
- `NontrivialZeroFamily gamma`: `rho_i = 1/2 + i gamma_i` are zeros of zeta in the open strip (exactly `TieIn`'s
  `StripZeros`), and each zero `z` of the strip occurs `analyticOrderAt riemannZeta z` times (counted with `Set.encard`).
- **`ContourShift c g`**: `ResidueShift` for every such family. This is the one classical input.

**Proved from it.**

| declaration | says |
|---|---|
| `laplace_vpt`, `laplace_one_sub`, `laplace_half` | the transform on the line `c` is the Fourier transform of the tilted test function; `H_g(1 - s) = H_{g~}(s)`; the critical-line form |
| `vline_reflect` | the functional equation: `vline(W_g, 1 - c) = -vline(W_{g~}, c)` |
| `vline_wInt` | on the line `c > 1`: `vline(W_g, c) = P(g) - A(g)/2` (prime sum minus half the real place) |
| **`explicit_formula`** | `sum_i H(rho_i) = H(1) + H(0) - (P(g) + P(g~)) + (A(g) + A(g~))/2`, the zero sum summable |
| `explicit_formula_even` | for even `g`: `sum_rho H(rho) = H(1) + H(0) - 2 P(g) + A(g)` |
| `explicit_formula_zeros` | the same for the nontrivial zeros, in the ledger's coordinate `gamma` |

Here `P(g) = sum_n Lambda(n) n^{-1/2} g(log n)` (`primeSum`) and
`A(g) = (1/2 pi i) integral_{(c)} (psi(s/2) - log pi) H(s) ds` (`archTerm`). The real-place term stays on the line `c`;
moving it to the critical line (the more common printed form) is a further Cauchy shift that only uses the analyticity of
`psi(s/2)` on `Re s > 0`, not done here and not needed for the tie.

## 4. Layer (c): the ledger's hypothesis, discharged for smoothed cells [Lean]

`TieIn.lean`'s `ExplicitFormula T t gamma sigma` says: the Toeplitz form of the moments `t` on cells `s` with coefficients
`c` equals Weil's zero pairing of the test function `T s c`. For point-mass cells (`gridTest`) the infinite case has no
explicit formula (point masses are not admissible); the smoothed version is the honest class:

- `smoothedTest Phi eps s c = Phi(z) sum_j c_j e^{i z j eps}`: the transform of `sum_j c_j phi(x - j eps)` for a cell profile
  with transform `Phi`.
- `KernelSpec Phi eps k`: the kernel `k_m` of the lag `m` has transform `Phi(z) conj Phi(conj z) e^{i z m eps}` on the
  critical line. For `k_m(x) = (phi * phi~)(x - m eps)` this is the convolution theorem (classical; stated as a hypothesis
  on the chosen kernels, not proved here).
- `efMoment c k m = efRHS c (k m)`: **the prime-side moment of the lag `m`**, the right side of the explicit formula for
  `k_m` (poles, `Lambda(n) n^{-1/2}`, real place). This is audit item 12 of `GRH-TIE-IN.md`: the moment sequence of the
  zeta column, now named concretely.

| declaration | says |
|---|---|
| `smoothed_pairing` | `F(z) conj F(conj z) = sum_{j,l} conj c_j c_l K_{l-j}(z)` for the smoothed test function |
| `explicitFormula_of_residueShift` | `ResidueShift` for every kernel gives `ExplicitFormula (smoothedTest Phi eps) (efMoment c k) gamma sigma`, any family closed under conjugation (bilinearity; the finite sums are exchanged with the absolutely convergent zero sums) |
| `explicitFormula_of_contourShift` | the same for the nontrivial zeros of zeta with multiplicity, from `ContourShift` |
| **`zeta_tie_in_contourShift`** | `ExtRH` + `ContourShift` (+ kernel regularity, `KernelSpec`, the symmetry `sigma`): `ScaleSign (efMoment c k)` and Weil's pairing nonnegative |

**Status of `GRH-TIE-IN.md` audit items after this round** (that file is not edited here; for the coordinator):
- item 10 (the explicit formula on the ledger's test class): reduced from an opaque identity on the grid to `ContourShift`,
  a statement in Mathlib's own vocabulary (`completedRiemannZeta`, `logDeriv`, Bochner integrals, `analyticOrderAt`), for
  zeta and smoothed cells. Dirichlet: not yet (section 6).
- item 11 (convergence): the zero sum's summability is now part of the named step and is used, not assumed vacuously; the
  pairing is no longer "nonnegative because `tsum` of a non-summable family is 0".
- item 12 (which moments): `efMoment`, concrete.
- items 8, 9 (the symmetry `sigma`, multiplicities): multiplicities are now pinned by `NontrivialZeroFamily`; `sigma` is
  still a hypothesis.

## 5. What is named, and what it would take [classical / open]

| named | where | classical source | what proving it takes |
|---|---|---|---|
| `ContourShift c g` | `ExplicitFormula.lean` | Weil 1952; Iwaniec-Kowalski Thm 5.12; Davenport ch. 17 | (1) residue theorem on rectangles for a function with finitely many simple poles (subtract the principal parts; Mathlib has the Cauchy-Goursat theorem for rectangles); (2) zero count `N(T + 1) - N(T) = O(log T)` (Jensen's formula, now in Mathlib, applied to `xi` with the growth bound `log abs xi(s) = O(abs s log abs s)`, which needs Stirling for complex Gamma and a convexity bound for zeta in the strip); (3) the local partial-fraction bound `zeta'/zeta(s) = sum_{abs(gamma - T) < 1} 1/(s - rho) + O(log T)` (Borel-Caratheodory / Landau's lemma), giving heights `T_k` with `abs(Lambda'/Lambda) = O(log^2 T_k)` on the horizontal sides; (4) decay of `H` in vertical strips for `g` in `C^2_c`; (5) the limit `T_k -> infinity` and absolute convergence of the zero sum from (2). A multi-round project, thousands of lines; parts may exist in the PrimeNumberTheoremAnd project [reading, not checked] |
| `EFTest` fields beyond `g = 0` | `ExplicitFormula.lean` | integration by parts | a lemma "`g` in `C^2_c` gives `H(c + it) = O(1/t^2)` uniformly in a strip" and `Gamma_R'/Gamma_R = O(log t)`; modest |
| `KernelSpec` | `ExplicitFormulaTie.lean` | convolution theorem | Mathlib's Fourier transform of a convolution, transported to the `e^{izx}` convention; modest |
| `sigma` with `gamma (sigma i) = conj (gamma i)` | `ExplicitFormulaTie.lean`, `TieIn.lean` | functional equation + conjugation | a bijection on an enumeration with multiplicity; needs `analyticOrderAt` invariance under `s -> 1 - conj s`; modest |
| `ExtRH` | `TieIn.lean` | external (others, Lean, 2026-11-20) | the audit list `GRH-TIE-IN.md` 2.3 |
| existence of a `NontrivialZeroFamily` | | zeros are discrete with finite orders (`isDiscrete_riemannZetaZeros` is in Mathlib) | countable enumeration with repetition; modest |

## 6. What is left beyond this round [open]

- **The contour shift** (section 5). The single named step between this formalisation and an unconditional explicit
  formula for zeta.
- **Dirichlet L-functions.** The same three layers for `L(chi, s)`: Mathlib has `LSeries_twist_vonMangoldt_eq`
  (`-L'/L = L(chi Lambda, s)`), and the functional equation of the completed Dirichlet L-function for primitive
  characters. New: the Gamma factor with the parity of `chi`, the conductor term `log(q/pi)`, the root number in the
  reflection (the line `1 - c` gives `chi-bar`, so the tie needs the pairing of `chi` with `chi-bar`), no pole terms for
  `chi != 1`. Layers (a) to (c) are mechanical given this file; the contour shift is the same analytic work.
- **The real place on the critical line** (the printed form). A Cauchy shift of `psi(s/2) H(s)` from `c` to `1/2`.
- **Point-mass cells.** `gridTest` (finite exponential sums) is not in any test class of the explicit formula; the
  infinite-case tie needs the smoothed cells of section 4, so the ledger's grid form and the smoothed form must be
  compared (smoothing scale against grid width). Not addressed.

## 7. Numerical check [numerical]

`explicit_formula_check.py` evaluates both sides of `explicit_formula` in exactly the Lean normalisation (line `c = 2`,
`H`, `P`, `A`, reflection as in the Lean definitions) for `g(x) = exp(-(x - a)^2 / (2 sigma^2))`, with the first 200 zeros
(`gamma` up to 396). The Gaussian is not compactly supported; the classical formula holds for it, and the check is about
signs and normalisation.

| a | sigma | zero side | right side | abs diff |
|---|---|---|---|---|
| 0 | 0.15 | 0.0853455477944 | 0.0853455477944 | 2.5e-32 |
| 0 | 0.5 | 3.57357931261e-11 | 3.57357931261e-11 | 6.6e-31 |
| 0.3 | 0.5 | -1.62470308972e-11 | -1.62470308972e-11 | 6.0e-31 |
| 0.4 | 0.3 | 0.000151471154436 | 0.000151471154436 | 3.3e-31 |

`sigma = 0.15` is dominated by the zeros, `sigma = 0.5` by the primes and the real place (zeros contribute below
`e^{-24}`), `a != 0` tests the reflected terms. Control: the prime sum with the wrong sign misses by 1.02.

## 8. Upstreaming to Mathlib (a separate, outward step; nothing opened)

| piece | fit | what upstreaming needs |
|---|---|---|
| `logDeriv_Gammaℝ`, `logDeriv_completedZeta`, `logDeriv_completedZeta_one_sub` | next to `NumberTheory/LSeries/RiemannZetaLogDeriv.lean` | Mathlib style pass, `Gammaℝ` lemmas may belong in `Gamma/Deligne.lean` |
| `lineIntegral_LSeries_vonMangoldt` | `NumberTheory/LSeries/` (a smoothed Perron formula) | generalise from `Lambda` to any `f` with `LSeriesSummable f c` (the proof uses only that); state with `vpt` replaced by Mathlib's conventions for vertical integrals (`VerticalIntegrable`, `mellin`) |
| `explicit_formula` from `ResidueShift` | only after the contour shift is proved | a contour-shift lemma in Mathlib's complex analysis, then the assembly here |

No pull request was opened anywhere.

## 9. What this does not do

- It does **not** prove RH or GRH, and it does not give the sign from the primes alone. The ledger's sign in
  `zeta_tie_in_contourShift` comes from `ExtRH` through the easy direction.
- It does **not** prove the explicit formula unconditionally: the contour shift is a named classical hypothesis.
- It covers **zeta only**; the Dirichlet column still names its explicit formula as in `GRH-TIE-IN.md`.
- The test class is shown nonempty only by `g = 0`; nontrivial members need the decay lemma of section 5.
