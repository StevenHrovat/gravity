# The contour shift for zeta in Lean: the explicit formula with no named step

Status: 2026-11-24. Follows `EXPLICIT-FORMULA.md` (sections 3 and 5: the one named step `ContourShift`). Under the
construction principle: content from the best existing results, cited and audited; the project builds what is missing.

Files:
- Lean (`docs/mass-gap/formal/ProofPhase/GRH/`), in two parts:
  - **The Mathlib-only core, destined for IM** (namespace `ProofPhase.GRH.CS`; imports only Mathlib v4.34.0 and each
    other): `ContourShiftRect.lean` (rectangles), `ContourShiftLandau.lean` (log-derivative bound, zero count),
    `ContourShiftZeta.lean` (zeta), `ContourShiftTest.lean` (test functions), `ContourShift.lean` (the contour shift).
  - **The project tie** (namespace `ProofPhase.GRH.CSTie`; imports the core and `ExplicitFormulaTie`):
    `ContourShiftTie.lean` (the core theorem as the project's `EF.ContourShift`, the test class, the explicit formula,
    the ledger's zeta column). Build target `ProofPhase.GRH.ContourShiftTie`.
- `ContourShiftExists.lean` (project side, namespace `CSTie`): a concrete enumeration of the nontrivial zeros with
  multiplicity, so the explicit formula's hypothesis on `γ` is not vacuous.
- `contourshift-axioms.sh` and `contourshift-axioms.log`: 122 declarations, all on the standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`), no `sorry`, no `native_decide`, no warnings in the seven files; the log also lists
  the imports of the core files (Mathlib and the core only). About 2350 lines.

Status marks as in `OPEN-STEPS-DMP.md`: **Lean**, **classical**, **external**, **numerical**, **reading**, **open**.

---

## 0. In plain words

**What was missing.** The explicit formula for zeta (`EXPLICIT-FORMULA.md`) was proved in Lean from one classical step,
the *contour shift*: the difference of the two vertical line integrals of `-Lambda'/Lambda * H` equals the residues in
between (`H(1) + H(0)` from the poles, `-H(rho)` for each zero), with the zero sum converging absolutely. Mathlib had
Cauchy's theorem for rectangles but no residue theorem, no growth bound for zeta in strips, no zero count and no bound
for `zeta'/zeta` near the zeros.

**What is now true.** The contour shift is a theorem (`CS.contourShift`, and as the project's statement
`CSTie.contourShift_EF`) for every line `c > 1` and every test function
`g` that is smooth with compact support. With it, **Weil's explicit formula for zeta holds in Lean with no named step**
(`explicit_formula_smooth`, `explicit_formula_of_smooth`): for every enumeration of the nontrivial zeros with
multiplicity, `sum over zeros of H(rho)` converges absolutely and equals the pole terms minus the prime sum plus the
real place. The zeta column of the ledger (`zeta_tie_in_smooth`) now needs, besides `ExtRH`, only the kernel
bookkeeping (`KernelSpec`, the symmetry `sigma`), no analytic hypothesis.

**How.** The classical proof (Iwaniec-Kowalski Thm 5.12; Davenport ch. 17) uses sharp bounds: `N(T+1) - N(T) = O(log T)`
and `zeta'/zeta = O(log^2 T)` on good horizontal lines, which need Stirling's formula and a convexity bound. A smooth
compactly supported test function has a transform `H` that decays faster than any power in vertical strips, so
**polynomial bounds are enough**, and those come cheaply:
- the completed zeta minus its poles is bounded on every vertical strip, directly from Mathlib's definition of it as a
  Mellin transform (no convexity bound, no Stirling);
- one lower bound at the points `2 + iy`, from the reflection formula `|Gamma(1 + ix)|^2 = pi x / sinh(pi x)` and
  `|zeta(2 + iy)| >= 2 - pi^2/6`;
- the maximum principle then counts the zeros near each height (at most `B (1 + |y|)^2` per unit window, weaker than
  the classical `O(log T)` and enough), and Landau's lemma, proved with Mathlib's Borel-Caratheodory theorem, bounds
  `Lambda'/Lambda` polynomially on the vertical lines and on horizontal segments chosen between the zeros;
- the argument principle on rectangles, built here, gives the residues; the limits are dominated convergence and an
  exhaustion of the absolutely convergent zero sum.

No Hadamard product, no Riemann-von Mangoldt formula, no zero-free region beyond `Re s = 1` is used.

**What this does not do.** It does not prove RH or GRH, and nothing here gives the sign of the ledger; that still comes
from `ExtRH` through the easy direction. The test class is `C^infinity` with compact support, not `C^2` with compact
support (section 5). Dirichlet L-functions are not done (section 5).

---

## 1. The layer plan and its status

| layer | content | file | status |
|---|---|---|---|
| (a) | residue calculus on rectangles: `∮ 1/(s - a) = 2πi`, Cauchy's formula, factoring out zeros, the argument principle with a weight | `ContourShiftRect.lean` | **Lean** |
| (b) | Landau's lemma (log-derivative near the zeros), zero count on discs, choice of heights; for zeta: `ξ`, strip bound, lower bound, `Λ'/Λ` polynomial on the lines and at good heights | `ContourShiftLandau.lean`, `ContourShiftZeta.lean` | **Lean** |
| (c) | zero count per unit window, `O((1 + \|y\|)^2)` | `ContourShiftZeta.lean` (`zero_count_window`) | **Lean** |
| (d) | test functions: `H` entire, rapid decay in strips; the assembly: the contour shift (core); the test class, the explicit formula, the tie (project) | `ContourShiftTest.lean`, `ContourShift.lean` (core); `ContourShiftTie.lean` (project) | **Lean** |

## 1a. The Mathlib-only core, destined for IM [Lean]

On the owner's rule (2026-11-24: what Mathlib lacks is also implemented in IM, which must work with Mathlib and Lean
4.34 alone), the round is split in two.

**Core (for IM):** `ContourShiftRect.lean`, `ContourShiftLandau.lean`, `ContourShiftZeta.lean`, `ContourShiftTest.lean`,
`ContourShift.lean`. They import only Mathlib v4.34.0 and each other, never a project module, never PrimeNumberTheoremAnd.
Where the project already had a definition or a short lemma, the core repeats it with the same body: `laplace`, `vpt`,
`vline`, `wInt`, `ZeroFamily` (= `EF.NontrivialZeroFamily`), `differentiableAt_Gammaℝ'`. Its headline is
`CS.contourShift`, stated in that vocabulary. Checked twice: the axioms log lists the core's imports, and the five files
were built alone in a fresh Lake project that has only Mathlib v4.34.0 as a dependency (`Build completed successfully`).
Moving them to IM is a rename of the module paths (`ProofPhase.GRH.ContourShift*`) and of the namespace; nothing else
changes.

**Tie (stays in this repository):** `ContourShiftTie.lean`. Because the repeated definitions have the same bodies,
`CSTie.contourShift_EF : EF.ContourShift c g` is the core theorem applied as it stands (a definitional
identification). The rest of the tie (`efTest_of_smooth`, `explicit_formula_smooth`, `explicit_formula_of_smooth`,
`zeta_tie_in_smooth`) uses the project's `ExplicitFormula*.lean` and `TieIn.lean`. Once the core lives in IM, the tie
imports it from there and the project's own copies of `laplace`, `vline`, ... could become those of IM.

## 2. Inventory: what existed, where

### 2.1 Mathlib (v4.34.0, commit `5ed2965256430c3649e86755f9576b54eca72435`) [Lean; read in the pinned tree]

Used, and more than the plan of `EXPLICIT-FORMULA.md` section 5 expected:

| ingredient | Mathlib | used for |
|---|---|---|
| Cauchy's theorem on rectangles | `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` (and the off-countable version) | all rectangle integrals |
| removable singularities | `dslope`, `differentiableOn_dslope` | Cauchy's formula on rectangles |
| factoring zeros of a meromorphic function on a compact set | `MeromorphicOn.extract_zeros_poles`, `MeromorphicOn.divisor` (Kebekus) | `exists_factor` |
| logarithmic derivatives | `logDeriv_mul`, `logDeriv_fun_prod`, `logDeriv_fun_pow`, `logDeriv_congr_nhds` | the argument principle, Landau |
| Borel-Caratheodory | `Complex.borelCaratheodory` (Radziwill, 2026) | Landau's lemma |
| primitives on discs (Morera) | `DifferentiableOn.isExactOn_ball` (Jauslin, Kontorovich, Nash) | holomorphic logarithm on a disc |
| maximum modulus, Cauchy estimate | `Complex.norm_le_of_forall_mem_frontier_norm_le`, `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` | Landau's lemma, the zero count |
| Jensen's formula and inequality | `MeromorphicOn.circleAverage_log_norm`, `AnalyticOnNhd.sum_divisor_le` (Kebekus) | available; the max-modulus count was simpler here |
| canonical (Blaschke) decomposition | `MeromorphicOn.exists_canonicalDecomp` (Kebekus) | available, not needed |
| completed zeta as a Mellin transform | `completedRiemannZeta₀`, `WeakFEPair.Λ₀ = mellin f_modif`, `IsStrongFEPair.hasMellin` | the strip bound |
| zeta basics | `completedRiemannZeta_eq`, `completedRiemannZeta_one_sub`, `riemannZeta_def_of_ne_zero`, `riemannZeta_ne_zero_of_one_le_re`, `zeta_eq_tsum_one_div_nat_add_one_cpow`, `riemannZeta_two` / `hasSum_zeta_two` | `ξ` and its zeros, the lower bound |
| zeros discrete, finite on compacts | `isDiscrete_riemannZetaZeros`, `IsCompact.inter_riemannZetaZeros_finite` (Zheng, 2026) | finite zero sets in rectangles |
| Gamma | `Gamma_mul_Gamma_one_sub`, `Gamma_add_one`, `Gamma_conj` | `\|Gamma(1 + ix)\|^2 = pi x / sinh(pi x)` |
| integrals | dominated differentiation (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), integration by parts on the line (`integral_mul_deriv_eq_deriv_mul_of_integrable`), `intervalIntegral_tendsto_integral`, `integrable_one_add_norm` | `H` entire and decaying; the limits |

Missing in Mathlib (and built here): a residue theorem or argument principle on rectangles; Landau's lemma; any bound
for `zeta`, `Lambda` or `zeta'/zeta` in a strip as a lemma; a zero count for zeta; the explicit formula. Also absent and
not needed: the Hadamard product of `ξ`, the Riemann-von Mangoldt formula, a zero-free region inside the strip.

### 2.2 PrimeNumberTheoremAnd (PNT+; Kontorovich, Tao and others; Apache 2.0) [reading]

Read at commit `a4fb6989b07e9c76b511807ae93e33e25b820e9b` (2026-11-15), file headers and statement lists, not the proofs.
Its toolchain is Lean `v4.35.0`, one version ahead of this repository's `v4.34.0` pin.

| PNT+ file | what it has | relation to this round |
|---|---|---|
| `ResidueCalcOnRectangles.lean`, `Rectangle.lean` | the residue theorem for simple poles on rectangles (`RectangleIntegral'_eq_sumResiduesIn`) | the same ground as layer (a); written independently here, in Mathlib's four-sided rectangle form |
| `RectangleArgumentPrinciple.lean` | the argument principle on rectangles via `meromorphicOrderAt` (`rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt`) | the unweighted form of `rectInt_logDeriv_mul` |
| `BorelCaratheodory.lean` | Borel-Caratheodory | now in Mathlib in substance (used from there) |
| `ZetaBounds.lean` | Euler-Maclaurin bounds for `zeta` near `Re s = 1` | not needed (the Mellin strip bound replaces it) |
| `Backlund/ZeroCountCrude.lean` | `\|N(T)\| <= A T^(3/2)` via the Hadamard machinery and a growth bound for `(s - 1) zeta(s)` | same kind of crude polynomial count as `zero_count_window`, by a different route |
| `Mathlib/NumberTheory/LSeries/RiemannZetaHadamard.lean`, `Mathlib/Analysis/Complex/HadamardFactorization*` | Hadamard factorization of `ξ` (order one) and the zero-sum identity for `ξ'/ξ` | not needed |
| `IEANTN/KadiriZeroCounting.lean`, `IEANTN/HadamardLogDerivative.lean` | zero counting and square-tail summability for Kadiri's explicit-formula work, with Riemann-von Mangoldt as a hypothesis with Backlund's constants | toward explicit formulas for `psi(x)`; I found no Weil-type explicit formula for a test-function class there |

**Dependency decision for the coordinator.** Nothing from PNT+ is used, vendored or copied; the round needed only
Mathlib. A Lake dependency on PNT+ would need a PNT+ commit built on Lean `v4.34.0` with a Mathlib compatible with this
repository's pin (PNT+ has moved to `v4.35.0`), and would pull in its blueprint tooling and a large tree; there is no
reason to add it for this step. Credit: the rectangle argument principle and the crude zero count cover the same ground
as PNT+'s files (Kontorovich and others); they were written here independently on Mathlib's API (PNT+'s proofs were not
read). The Borel-Caratheodory theorem used is Mathlib's (Radziwill). The core (section 1a) has no PNT+ dependency and
builds with Mathlib alone.

## 3. Layer (a): residue calculus on rectangles [Lean]

`rectInt f z w` is the counterclockwise integral around the rectangle with corners `z`, `w`, in exactly the four-sided
form of Mathlib's Cauchy theorem.

| declaration | says |
|---|---|
| `rectInt_congr`, `rectInt_add`, `rectInt_sum`, `rectInt_const_mul`, `rectInt_eq_zero` | the integral depends only on the boundary values; linearity; Cauchy's theorem |
| **`rectInt_inv_sub`** | `∮ (s - a)^(-1) ds = 2πi` for `a` strictly inside (four principal logarithms; the argument jumps by `π` twice on the left side) |
| **`rectInt_div_sub`** | Cauchy's formula `∮ H(s)/(s - a) ds = 2πi H(a)` for `H` entire |
| **`exists_factor`** | an entire `F`, not identically zero, equals `prod_rho (s - rho)^(ord_rho F) * q(s)` on a compact convex `K` with nonempty interior, `q` analytic near `K` without zeros on `K` (Mathlib's `extract_zeros_poles`, made pointwise by the identity theorem) |
| `logDeriv_prod_pow_mul` | `(P q)'/(P q) = sum ord/(s - rho) + q'/q` |
| **`rectInt_logDeriv_mul`** | the argument principle with a weight: `F` entire with no zero on the boundary, `H` entire: `∮ (F'/F) H = 2πi sum_rho ord_rho(F) H(rho)` over the zeros in the rectangle |

## 4. Layer (b), generic: Landau's lemma [Lean]

For `f` entire, `f(z0) != 0`, `|f| <= M` on `|z - z0| <= R`, `L = log(M/|f(z0)|)`:

| declaration | says |
|---|---|
| `exists_log_ball` | a holomorphic function without zeros on a disc has a holomorphic logarithm there (primitive of `q'/q`) |
| **`landau`** | the zeros with `\|rho - z0\| <= R/3` number at most `L / log 2` (with multiplicity), and for `\|z - z0\| <= R/12`, `f(z) != 0`: `\|f'/f(z) - sum ord/(z - rho)\| <= 24 (L + 1)/R` (Landau's lemma; Titchmarsh, section 3.9) |
| `norm_logDeriv_le` | hence `\|f'/f(z)\| <= 24 (L + 1)/R + L/(delta log 2)` if `z` keeps distance `delta` from those zeros |
| `exists_far_point` | among `N` reals some point of `[a, a + 1]` keeps distance `1/(2(N + 1))` from all of them (pigeonhole) |

Proof of `landau`: factor out all zeros in the disc of radius `R` (`exists_factor`) and put the outer ones back into
`q`; on the circle `|z - rho| >= 2R/3` and at the centre `|z0 - rho| <= R/3` for the inner zeros, so the maximum
principle gives both `2^N <= M/|f(z0)|` (the count) and `|q(z)/q(z0)| <= M/|f(z0)|` on the disc; the holomorphic
logarithm of `q/q(z0)` on radius `R/3` has real part at most `L`; Borel-Caratheodory bounds it by `2(L + 1)` on radius
`R/6`; Cauchy's estimate bounds its derivative `q'/q` by `24(L + 1)/R` on radius `R/12`.

## 5. Layers (b), (c) for zeta [Lean]

| declaration | says |
|---|---|
| `norm_mellin_le_of_strip`, **`exists_bound_completedZeta₀`** | a Mellin transform convergent at `a` and `b` is bounded on `a <= Re s <= b`; hence `Λ₀` is bounded on every vertical strip |
| `xiF`, `differentiable_xiF`, `xiF_eq` | `ξ(s) = s(s - 1)Λ₀(s) + 1 = s(s - 1)Λ(s)`, entire |
| **`xiF_eq_zero_iff`**, **`analyticOrderAt_xiF`** | the zeros of `ξ` are exactly the zeros of `zeta` in `0 < Re s < 1`, with the same orders |
| `logDeriv_completedZeta_eq` | `Λ'/Λ = ξ'/ξ - 1/s - 1/(s - 1)` |
| `norm_sq_Gamma_one_add_I_mul`, `norm_Gamma_one_add_I_mul` | `\|Γ(1 + ix)\|^2 = πx/sinh(πx)`, hence `\|Γ(1 + ix)\| >= e^(-π\|x\|/2)` |
| `norm_zeta_two_add`, `norm_xiF_two_add` | `\|zeta(2 + iy)\| >= 2 - π^2/6`; `\|ξ(2 + iy)\| >= (2/π)(2 - π^2/6) e^(-π\|y\|/4)` |
| `xi_data` | on the disc of radius `R` about `2 + iy`: `log(max\|ξ\| / \|ξ(2 + iy)\|) <= A (1 + \|y\|)^2` |
| `zero_count_ball`, **`zero_count_window`** | at most `B (1 + \|y\|)^2` zeros (with multiplicity) within `R/3` of `2 + iy`, and with `\|Im rho - y\| <= 1` |
| `logDeriv_xi_ball` | `\|ξ'/ξ(z)\| <= B (1 + \|y\|)^2 (1 + 1/delta)` near `2 + iy`, `delta` the distance to the zeros |
| **`logDeriv_vline_bound`** | `\|Λ'/Λ\| <= B (1 + \|y\|)^2` on `Re s = c` and on `Re s = 1 - c` (`c > 1`) |
| **`exists_good_height`** | every `[a, a + 1]` with `a >= 1` or `a <= -2` contains `T` with no zero on `[1 - c, c] + iT` and `\|Λ'/Λ\| <= B (1 + \|a\|)^4` there |

## 6. Test functions [Lean]

For `g : R -> C` and `H(s) = ∫ g(x) e^((s - 1/2) x) dx` (`EF.laplace`):

| declaration | says |
|---|---|
| `differentiable_laplace` | `H` is entire (`g` continuous with compact support) |
| `norm_laplace_le` | `\|H(s)\| <= ∫ \|g\| e^(K\|x\|)` on `\|Re s - 1/2\| <= K` |
| `laplace_deriv`, `laplace_iteratedDeriv` | `(s - 1/2)^k H_g(s) = (-1)^k H_{g^(k)}(s)` (integration by parts on the line) |
| **`laplace_decay`** | for `g` smooth with compact support: `\|H(s)\| (1 + \|Im s\|)^k <= C(k, K)` on every strip, every `k` |

Smoothness is stated as `∀ k : ℕ, ContDiff ℝ k g`; `contDiff_nat_of_smooth` converts `ContDiff ℝ ∞ g` to it.

## 7. The assembly [Lean]

Core (`ContourShift.lean`, namespace `CS`) and tie (`ContourShiftTie.lean`, namespace `CSTie`).

| declaration | says |
|---|---|
| `rect_identity` | on `[1 - c, c] × [b, t]` with zero-free horizontal sides: `∮ (-Λ'/Λ) H = 2πi (H(1) + H(0) - sum ord_rho H(rho))` |
| `integral_line_eq_vline`, `integrable_wInt_line` | `∫ f(x + iy) dy = 2π vline f x`; the integrand is `O((1 + \|y\|)^(-2))` on both lines |
| `zf_fiber_card`, `zf_sum`, **`zf_summable`**, `zf_tendsto` | for a `NontrivialZeroFamily`: each zero occurs `ord` times; sums over the indices landing in a finite set of zeros are sums with multiplicity; `∑_i H(rho_i)` is absolutely summable (windows of height one, `zero_count_window`, `\|H\| <= C (1 + \|Im\|)^(-4)`); the sums over the zeros in growing rectangles tend to it |
| **`contourShift`** (core) | the contour shift for `c > 1` and `g` smooth with compact support, in the core's vocabulary |
| **`contourShift_EF`** (tie) | the same as the project's `EF.ContourShift c g` (definitional identification) |
| **`efTest_of_smooth`** (tie) | such `g` satisfy `EF.EFTest c g` (the test class is not only `g = 0` any more) |
| **`explicit_formula_smooth`**, **`explicit_formula_of_smooth`** (tie) | Weil's explicit formula for `zeta` with no named step |
| **`exists_nontrivialZeroFamily`**, **`explicit_formula_zetaZeros`** (`ContourShiftExists.lean`) | the index set of pairs `(z, k)`, `z` a zero in the strip, `k < ord_z ζ`, with `γ = -i(z - 1/2)`, is a `NontrivialZeroFamily` (`nontrivialZeroFamily_zetaZeroOrdinate`); the explicit formula for this enumeration, nothing assumed about `γ` |
| **`zeta_tie_in_smooth`** (tie) | `ExtRH` + `KernelSpec` + `sigma`, for smooth compactly supported kernels: `ScaleSign (efMoment c k)` and Weil's pairing nonnegative |

The heights: `t_n ∈ [n + 1, n + 2]` and `b_n ∈ [-(n + 2), -(n + 1)]` from `exists_good_height`; on these sides
`|(-Λ'/Λ) H| <= 64 B C / (n + 1)^2` (`horiz_side_le`, with `laplace_decay` at `k = 6`), so the horizontal sides tend to
`0`; the vertical sides tend to `2π` times the line integrals; the zero sums tend to the sum over the family; the two
limits of the same sequence agree.

**Numerical status.** The statement of `ContourShift` is unchanged from `EXPLICIT-FORMULA.md`; its numerical check
there (section 7, 200 zeros, four Gaussian test functions, agreement to 30 digits, the control with the wrong prime sign
off by 1) applies unchanged [numerical; not re-run].

## 8. What remains [open]

- **The test class `C^2_c`.** The theorem covers `C^∞_c`. Iwaniec-Kowalski's class `C^2_c` gives only `H = O(1/t^2)`,
  which needs the sharp classical bounds: `N(T + 1) - N(T) = O(log T)` (Jensen with Stirling for `Γ` in strips and the
  growth of `zeta` of order one) and `Λ'/Λ = O(log^2 T)` at good heights (Landau's lemma as here, with the sharp count).
  Estimated 600 to 1000 lines on top of these files (Stirling for complex `Γ` in strips is the larger part). Not needed
  for the ledger: smoothed cells with a smooth profile `φ` give kernels `(φ * φ~)(x - mε)` that are smooth with compact
  support, so `zeta_tie_in_smooth` applies.
- **Dirichlet L-functions.** The same three layers. Reusable as they are: `ContourShiftRect`, `ContourShiftLandau`,
  `ContourShiftTest`, the zero-family part of `ContourShift`. New: the strip bound for the completed `L(chi, s)` (Mathlib
  builds it from Hurwitz FE pairs, so `norm_mellin_le_of_strip` applies), the lower bound at `2 + iy`
  (`|L(2 + iy, chi)| >= 2 - zeta(2)` and the Gamma factor with the parity of `chi`), no pole terms for `chi != 1`, the
  root number in the reflection. Estimated 600 to 900 lines; layers (a) to (c) of `EXPLICIT-FORMULA.md` for Dirichlet
  (section 6 there) come first.
- **The kernel bookkeeping** of the tie, unchanged: `KernelSpec` (the convolution theorem, stated on the chosen kernels)
  and the conjugation symmetry `sigma`; and `ExtRH`, external (`GRH-TIE-IN.md` 2.3).
- **The printed form of the real place** (the digamma term on the critical line): a further Cauchy shift of
  `ψ(s/2) H(s)` from `c` to `1/2`; with `rectInt` and the decay of `H` it needs only a polynomial bound for `ψ` in a
  strip. Not needed for the tie.

**For the coordinator** (files not edited here): `EXPLICIT-FORMULA.md` sections 0, 1 (layer (d)), 5, 6 and 9 describe
`ContourShift` as named and the test class as `g = 0` only; both are now theorems for `C^∞_c` (`contourShift`,
`efTest_of_smooth`; `CSTie.contourShift_EF` is `EF.ContourShift`). `GRH-TIE-IN.md` audit item 10 (the explicit formula on the ledger's test class): for zeta and
smoothed cells with smooth profiles it is now a theorem (`zeta_tie_in_smooth`); item 11 (convergence of the zero sum):
proved, not assumed (`zf_summable`). `ExplicitFormula.lean`'s docstrings still call `ContourShift` a named hypothesis;
the definition stays (it is the statement proved here).

## 9. Upstreaming (a separate, outward step; nothing opened)

Pieces that would make sensible Mathlib contributions, roughly in the order they depend on each other:

| piece | where in Mathlib | form |
|---|---|---|
| `rectInt_inv_sub`, `rectInt_div_sub`, `rectInt_logDeriv_mul` (residue calculus on rectangles) | `Analysis/Complex/CauchyIntegral.lean` or a new `Analysis/Complex/RectangleResidue.lean` | state with Mathlib's four-sided boundary expression and for `f` meromorphic near the closed rectangle (residues via `meromorphicOrderAt` / divisor); PNT+'s `ResidueCalcOnRectangles` covers the same ground, so a joint contribution with its authors is the natural path |
| `exists_factor` (pointwise `extract_zeros_poles` for analytic functions on compact convex sets) | `Analysis/Meromorphic/FactorizedRational.lean` | a corollary of `extract_zeros_poles` |
| `exists_log_ball` (holomorphic logarithm of a zero-free function on a disc) | `Analysis/Complex/HasPrimitives.lean` | generalise to simply connected domains once primitives exist there (the file's TODO) |
| `landau`, `norm_logDeriv_le` (Landau's lemma) | new `Analysis/Complex/LandauLemma.lean`, next to `BorelCaratheodory.lean` | state for `f` analytic on a closed disc rather than entire |
| `norm_mellin_le_of_strip`, `exists_bound_completedZeta₀` | `Analysis/MellinTransform.lean`; `NumberTheory/LSeries/RiemannZeta.lean` (and the Hurwitz/Dirichlet analogues) | for `WeakFEPair.Λ₀` in general |
| `norm_sq_Gamma_one_add_I_mul` | `Analysis/SpecialFunctions/Gamma/Beta.lean` | `\|Γ(1 + ix)\|^2 = πx / sinh(πx)` |
| `xiF` with `xiF_eq_zero_iff`, `analyticOrderAt_xiF`, `zero_count_window` | `NumberTheory/LSeries/ZetaZeros.lean` | under the name `riemannXi`, as PNT+ calls it |
| `laplace_decay` | `Analysis/Fourier/` | the Paley-Wiener direction for `C^∞_c`: rapid decay uniformly in strips |
| `contourShift`, `explicit_formula_smooth` | `NumberTheory/LSeries/ExplicitFormula.lean` (new) | after the pieces above; with the test class `C^∞_c`, `C^2_c` later |

No pull request was opened anywhere; upstreaming is the owner's decision.

## 10. What this does not do

- It does **not** prove RH or GRH. The explicit formula is an identity between zeros and primes; the ledger's sign in
  `zeta_tie_in_smooth` still comes from `ExtRH` through the easy direction.
- It covers **zeta only**, and the test class `C^∞_c` (section 8).
- The PNT+ inventory (section 2.2) is a reading of file headers and statement lists at one commit, not an audit of the
  proofs.
