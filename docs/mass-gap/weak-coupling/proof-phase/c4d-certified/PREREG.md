# Pre-registration: certified W1 column for the measured blocked action (cycle 4, workstream 4, 2026-11-22)

**Status: written before any certified run.** What I had seen when writing: the cycle-3 refit result (`../c3b-refit/PREREG.md`,
Result section; `runs-gpu/refit_summary.json`, `analysis.log`), `analyse_refit.py`, the c3c method and numbers
(`../c3c-certified/NOTE.md`, `cert_adjoint.py`), `AdjointW.lean`. Run so far: `check_structure.py` (neighbour structure, seconds).
No certified number of this workstream existed.

## Question

> Is the W1 Dobrushin column of the **fitted, truncated blocked action actually measured at L sqrt(sigma) = 2.80** (SU(2), good
> blocking, beta = 2.3, b = 8) below 1, **nonlinearly** (supremum over all single-link conditional laws), both halves included?

The cycle-3 number 0.676 was a *linearised* value: it used the uniform-law constants k_F = 8/(9 pi) per unit coupling, i.e. it
assumed the conditional laws are Haar. The conditional law of a spatial link has a field `|A| <= 0.8` (sum of staples weighted by
the couplings), far from uniform. This workstream replaces the linearisation by a bound valid for every conditional law.

## The object (fixed before the run)

* Link `i` of type temporal (t) or spatial (s). Single-link conditional density w.r.t. Haar on S^3 (SU(2)):
  `rho_i(u) ~ exp(Phi_i(u))`, `Phi_i(u) = sum_{p ni i} phi_p(<u, s_p>) + sum_{R ni i} beta_R <u, s_R>`, `s_p, s_R` unit
  quaternions (staples), `phi_p(t) = bF t + (bA/3)(4 t^2 - 1) + bT (2 t^3 - t)` with the couplings of the plane class of `p`
  (ts: plane contains the time direction, ss: otherwise). Plaquette counts: temporal link 6 ts; spatial link 2 ts + 4 ss; each
  link lies in 18 rectangles (1x2) with 5 other links each (pair table of `analyse_refit.py`, checked by `check_structure.py`:
  every link `i != z` shares at most one plaquette with `z`; sums 18/0 (t), 6/12 (s) over neighbours, 90 rectangle incidences).
* Moving link `z` (sharing factor `f` with `i`) by geodesic distance `d` moves the staple `s_f` along a geodesic at unit speed;
  `d/dd log rho_i = phi_f'(<u, s_f>) <u, b> - mean`, `b` unit, `b perp s_f`. So (as c3c, Sec. 3.1)
  `c(i, z) <= sum_{f ni i, z} N_f`, `N_f = sup || (phi_f'(<u,s>) <u,b> - E)rho_i ||_KR`, and the **column of z** is
  `sum_i c(i, z)`. Structure identical to the Lean column of `AdjointW.lean` (`common i z` counts shared plaquettes, `<= 18`
  neighbours-with-multiplicity); `analyse_refit.py` and the Lean file agree (checked); the only differences: the Lean file has
  one coefficient for all plaquettes (no ts/ss split) and no rectangles.
* **Relaxation:** `b` is any unit vector (not only `b perp s_f`), the field `A` is any vector with `|A| <= a` (a = max over link
  types of the sum of the |fundamental couplings| through a link, rectangles included).

## The method (all of it paper + interval arithmetic, one dimension)

For the pure-fundamental reference law `rho_A ~ exp(<A,u>)`, `|A| = r`, and `f = <u,b>`, `c = cos(angle(A,b))`:
Bessel closed forms (`x(r) = E cos t = I2/I1`, `q(r) = E cos^2 t = 1 - 3 I2/(r I1)`, `Z(r) = E_Haar e^{<A,u>} = 2 I1/r`,
`zeta = Z(2r)/Z(r)^2 = ||rho_A||_2^2`). With `g = (f - m) rho_A`, `m = E_A f = c x(r)`:
`||g||^2 = zeta V`, `V = c^2 (q(2r) - 2 x(r) x(2r) + x(r)^2) + (1 - c^2)(1 - q(2r))/3`;
degree-1 part `||g_1||^2 = 4 (c^2 (q - x^2)^2 + (1 - c^2)((1 - q)/3)^2)`;
`||g||_KR <= ||g||_{H^-1} <= sqrt( ||g_1||^2/3 + (||g||^2 - ||g_1||^2)/8 )` (Laplace eigenvalues 3 at degree 1, >= 8 above; no
degree 0). Everything is **linear in `c^2`**, so the sup over the direction is at `c^2 in {0, 1}`.
Perturbation by the centre-blind and cubic couplings (weight `w = exp(Psi)`, `rho = rho_A w / E w`, osc `Psi <= Dq := sum_p (4|bA|/3 + 2|bT|)`
over the plaquettes of a link): `|rho/rho_A - 1| <= eps := e^{Dq} - 1`, and
`||g' - g||_KR <= eps ( sqrt(zeta V) + E|f| (1 + eps) sqrt(zeta) ) / sqrt 3`. Adjoint term (`h = <u,a><u,b>`, `|h| <= 1/2`):
`N_h <= (1 + eps) sqrt(zeta) / sqrt 3`; cubic term (`|(6t^2 - 1) s| <= (10/3) sqrt(5/18)`): `N_g <= 2 (10/3) sqrt(5/18) (1+eps) sqrt(zeta)/sqrt 3`.
`N_F^* = sup_{r <= a, c^2 in {0,1}}` of the bound, `zeta^* = sup_{r <= a} zeta`. Per factor:
`k_p = |bF| N_F^* + (8|bA|/3) N_h + |bT| N_g`, `k_R = |bR| N_F^*`. **Column** (max over z type):
`t: 18 k_ts + 90 k_R`; `s: 3 (2 k_ts + 4 k_ss) + 90 k_R`. (All neighbours are charged with the sup over all link types: monotone, slightly
conservative.) One-dimensional interval arithmetic (mpmath `iv`, 100 bit; power series of `I1, I2` with nonnegative terms and an explicit
tail bound) on 1/400 cells of `r in [0, a]`. Everything is monotone in the coupling bounds, so the box is covered by its corner.

## The box (fixed now; contains the +-3 sigma box of **every** one of the four fits; bounds rounded up)

| coupling | central fit (base) | sigma | box bound |
|---|---|---|---|
| b_F ts | 0.05396 | 1.2e-4 | **0.0545** |
| b_F ss | 0.17113 | 1.6e-4 | **0.1725** |
| b_A ts | -0.00060 | 1.4e-4 | **0.0011** |
| b_A ss | 0.00149 | 1.5e-4 | **0.0020** |
| b_T ts (ext_T) | -0.00009 | 2.5e-4 | **0.0009** |
| b_T ss (ext_T) | 0.00033 | 1.8e-4 | **0.0009** |
| b_R (ext_R) | 0.00840 | 4.3e-5 | **0.0086** |

(the statistical errors are tiny, so the +-3 sigma box is a few per mille wide; I therefore also report the **margin**: the same
column with every coupling bound multiplied by 1.1, 1.25, 1.5, 2.) Verdict per fit: **base** (b_F, b_A; b_T = b_R = 0), **ext_T**,
**ext_R**, **ext_TR**.

## The three possible outcomes, per fit

1. **CERTIFIED < 1** over the box: the computed upper bound on the column is < 1. Then the fitted truncated action satisfies the
   W1 Dobrushin condition (this is exactly the Lean hypothesis `CertifiedMeasured`, base and ext_T).
2. **Certified >= 1 somewhere in the box:** a *lower* bound on the best single-link column exceeding 1. This method gives upper
   bounds only; a lower bound would need explicit conditional laws (c3c's ceiling does this at beta_A >= 0.275). At these couplings
   the linearised column (a lower-bound-type value at the uniform law, 0.68-0.89) is below 1, so **outcome 2 cannot occur here**; I
   state this before running.
3. **INCONCLUSIVE:** upper bound >= 1 (or between 1 and the linearised value): the criterion is neither certified nor refuted at
   this resolution; I then say which refinement decides it (better perturbation treatment, exact transport for the centre-blind part).

Expectation stated before the run (not a criterion): base: certified (about 0.8); ext_T: certified; **ext_R: borderline**, because
its linearised value is already 0.886 and the nonlinear constant exceeds the uniform one (`>= 8/(9 pi)` by the `r = 0` end of the
sup); a verdict "inconclusive" for ext_R is likely.

## Checks (float, before the certified run is trusted)

* `x, q, Z` closed forms against numerical quadrature on S^3 (mpmath `quad`), `V`, `||g_1||`, `||g||` against quadrature for random
  `(r, c)`;
* the bound at `r = 0` equals c3c's value `sqrt(1/12) = 0.28868` and exceeds the exact `8/(9 pi) = 0.28294`;
* a Monte-Carlo sanity check is not needed (everything is one-dimensional).

## Claim discipline

Certified (interval arithmetic + paper reduction) means: for the **fitted, truncated, anisotropic effective action**, on the
coarse torus `(Z/NZ)^4` with SU(2) links, the single-link W1 influences are bounded as stated. This is not a statement about the
lattice Yang-Mills theory, nor about the true blocked action (that distance is `H1Local(Lip)`, truncation, and `ObsTransferPhys`),
and the fit's own closure residuals (caveat 3 of the cycle-3 Result) are not covered: the bound is about the action *as fitted*.
Substantive: the bound `N_F^*` (new nonlinear control of the fundamental channel; c3c had only a crude `e^a` bound there) and the
column; definitional: the corner arithmetic, the `norm_num` inequalities in Lean.

Runs: `cert_measured.py` (CPU, one process, `CUDA_VISIBLE_DEVICES=-1`, each run well under 30 min). No GPU job rerun, no change of the
refit's committed results.

## Amendments after the first run (2026-11-22; before any result was accepted)

The first run used the plain L^2 bounds for `N_h`, `N_g` written above; it gave base 0.763, ext_T 0.815, ext_R 0.9935, ext_TR 1.052 at the
box. Three changes followed, all before the reported run: (1) the direction maximum of main + perturbation is now the sum of the maxima (the
bound is concave in c^2); (2) the Bessel-series tail bound no longer assumes y <= 1.1; (3) `N_h`, `N_g` now use the decomposition
`(G - c) rho = G + [(G - c)(rho - 1) - c]` with the H^-1 norm of `G` at the uniform law plus an L^2 bound of the bracket
(`NOTE.md`, section 1 (v)). The three outcomes and the box are unchanged. The expectation "ext_R: borderline; inconclusive likely" was
only half right: with the refined small terms ext_R is certified (0.964) and ext_TR sits at 0.9999 (knife edge).
