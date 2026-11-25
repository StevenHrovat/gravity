# Pre-registration: positivity bootstrap for SU(2) lattice Yang-Mills (2026-11-21, written before any bound is computed)

**Why.** The owner's reading of DMP is that a complete system "certifies its existence by consistency alone". The bootstrap is the
physics method closest to that: it bounds expectation values using only consistency conditions, with no simulation. Positivity is
reflection positivity (the physics reading of DMP's "two witnesses", README section 3.1b) together with Hermitian (Gram) positivity;
the loop equations are the Schwinger-Dyson equations of the gauge-invariant measure. This file fixes the method, the checks and the
comparisons before any bound is computed. Literature followed: Kazakov and Zheng, arXiv:2203.11360 (SU(infinity)) and arXiv:2404.16925
(SU(2) in 2, 3, 4 dimensions; below "KZ"); Liu and Yang, arXiv:2601.04316; the SU(3) bootstrap arXiv:2502.14421; the abelian programme
arXiv:2404.17071. All code is written from scratch here; the papers are references for method and numbers only.

## 1. Conventions

- Wilson action S = -(beta/2) sum_p tr U_p (beta = 4/g^2), the same as `lattice/su2.py`. KZ write lambda = 8/beta.
- Observables w(C) = < (1/2) tr U_C > for closed lattice loops C; real for SU(2), w(C) = w(C^-1), |w(C)| <= 1, w(trivial loop) = 1.
- Plaquette u_P = w(1x1). Rectangular loops W(R,T). Creutz ratio chi(2) = -ln[ W(2,2) W(1,1) / W(1,2)^2 ].
- The bounds hold for any translation- and hypercubic-invariant infinite-volume Gibbs state of the Wilson action (and on any periodic
  lattice large enough that no loop used wraps around), because every constraint below is an exact identity or inequality there.

## 2. Method (fixed)

**Variables.** One real variable per class of closed loops of length at most L_max, modulo translations, the hypercubic group (axis
permutations and reflections), cyclic rotation, orientation reversal and free reduction (U U^-1 = 1).

**Loop equations (constraint family LE).** For every closed reduced path W based at a site y (in practice: every cyclically reduced
loop class with |W| <= L_max - 4, rotated to start at each of its vertices) and every one of the 2d links V leaving y, the
Schwinger-Dyson identity sum_a < nabla^a_V tr(T^a W) > = sum_a < tr(T^a W) nabla^a_V S >, with SU(2) Fierz identity and Mandelstam
identity tr A tr B = tr AB + tr AB^-1 to close it on single traces:

    sum_{V in W, W = A V B} [ 1/4 t(W) + 1/2 t(A (VB)^-1) ]  -  sum_{V^-1 in W, W = A V^-1 B} [ 1/4 t(W) + 1/2 t(A V^-1 B^-1) ]
      + (beta/8) sum_{staples S of V} [ t(W V S) - t(W S^-1 V^-1) ] = 0,      t = tr.

This includes the standard Makeenko-Migdal equations (V on W) and the "backtrack" equations (V not on W). An equation is used only if
all its loops have length <= L_max. Before use, the equations are checked numerically against Monte Carlo configurations in 2D and 4D
(residuals consistent with zero within errors); a failure stops the work until fixed.

**Positivity (constraint families).** Basis: closed reduced paths A_i based at the origin (open Wilson lines starting and ending at the
origin, with tails allowed), length <= l_pos (default l_pos = L_max/2), restricted to the half space for reflection positivity.
For SU(2) the operator Gram matrix of the matrix elements of A_i splits exactly into a singlet and an adjoint channel; both are imposed:
- **G (Hermitian):** M_ij = w(A_i^-1 A_j), N_ij = w(A_i A_j); M + N >= 0 and M - N >= 0 (M >= 0 is their sum; KZ use M >= 0).
- **RS (site reflection)** across the plane x_1 = 0, basis in x_1 >= 0: M_ij = w((rA_i)^-1 A_j), N_ij = w(rA_i A_j), M +- N >= 0.
- **RD (diagonal reflection)** x_1 <-> x_2, basis in x_1 >= x_2: same form.
- **RL (link reflection)** across the plane x_1 = 1/2: basis paths cross into x_1 >= 1 by the link (0 -> e_1), stay there and return by
  it; with the crossing links gauge-fixed to 1 the same form applies.
Symmetry block-diagonalisation (numerical, from the stabiliser group of each matrix) is used to make the blocks small; it does not
change the constraint. In 4D at L_max >= 14 the basis may be truncated (e.g. to paths in a 2D or 3D sublattice, as in
arXiv:2502.14421); any truncation only weakens the bounds and is recorded in the output JSON.

**SDP.** min and max of the target w(C) subject to LE and all positivity blocks. Solver: Clarabel (interior point; called directly
or through cvxpy 1.9.3), SCS as fallback. Every run writes its settings (d, beta, L_max, l_pos, families, counts, solver status,
timing) to `docs/mass-gap/results/bootstrap_*.json`.

**Rigour.** For each reported bound the dual certificate (equality multipliers y, PSD multipliers Z) is rounded to exact dyadic
rationals, Z is rebuilt as R R^T (exactly positive semidefinite by construction, in the unreduced basis with integer 0/1 coefficient
matrices), beta is taken as the exact decimal rational, and the bound b^T y - <Z, F_0> - ||rho||_1 is evaluated in exact integer /
rational arithmetic, where rho is the exact stationarity residual and the a priori bound |w(C)| <= 1 covers it. Report the floating
and the rigorous number; target: rigorous weaker by at most 1e-5 (reported whatever it is).

**Cutoffs planned.** 2D: L_max = 8, 12, 16 (20 if cheap). 4D: L_max = 8, 10, 12, then higher (with truncated bases) as far as the
laptop allows in hours; the largest completed L_max is reported, nothing is dropped.

## 3. Validation criteria (confirmatory)

**(a) 2D SU(2)** (infinite lattice, exact): at beta = 1, 2, 4, every interval [lower, upper] must contain the exact
u_P = I_2(beta)/I_1(beta) = 0.240194, 0.433127, 0.658047, and the exact W(R,T) = u_P^(RT) for every rectangular loop bounded
(at least W(1,2), W(2,2), and W(1,3) when L_max allows). Containment is tested with a tolerance of 1e-6 (solver accuracy) for the
floating bounds and with no tolerance for the rigorous bounds. Expected (KZ, 2D): bounds tighten quickly with L_max.

**(b) 4D SU(2):** the plaquette bounds at beta = 2.0, 2.3, 2.4, 2.5 must contain the Monte Carlo values within 2 standard errors:
- beta = 2.3: 0.60224 +- 0.00006 (`results/lattice_summary.json`, 10^4);
- beta = 2.4: 0.630002 +- 0.000013 (stored run `lattice/runs-gpu/ttl_b2.4_L16.npz`, 16^4, 20-bin error);
- beta = 2.5: 0.651964 +- 0.000006 (stored run `lattice/runs-gpu/ttl_b2.5_L20.npz`, 20^4, 20-bin error);
- beta = 2.0: no stored run and no value in Teper hep-th/9812187 (which starts at beta = 2.2); measured by a short new CPU run
  `bootstrap/mc_reference.py` (same action, 8^4 and 10^4, heat bath + overrelaxation; the value is fixed before the 4D bounds at
  beta = 2.0 are computed and recorded in `results/bootstrap_mc_reference.json`).
Agreement with KZ (comparable points, read off their Figure 1b, accuracy about +-0.01): L_max = 16 band at lambda = 3.48
(beta = 2.3) about [0.48, 0.66]; L_max = 24 points about [0.597, 0.656] (beta = 2.51), [0.549, 0.623] (beta = 2.30), [0.526, 0.608]
(beta = 2.20). Criterion: our interval at the same L_max overlaps KZ's (both are rigorous, so disjoint intervals would mean an error
on one side); at lower L_max ours must contain KZ's higher-L_max interval or overlap it. Narrower-than-KZ results at equal L_max are
possible (extra constraint families) and are reported as such, not as a failure.

**(c) Widths:** reported for every beta and L_max (upper - lower), with the relative width (upper - lower)/MC.

**Verdict.** (a) and (b) hold at every point: **validated**. Any interval that misses its reference value: **fail** for that point,
reported with the cause if found; the code is then fixed and the full table re-run (the failure stays reported).

## 4. Exploratory part (labelled exploratory; no pass/fail verdict)

1. Bounds on W(1,2), W(2,2) (and W(1,3), W(2,3) where L_max allows) at beta = 2.3 and 2.4.
2. Bounds on the Creutz ratio chi(2): the joint allowed region of (W(1,1), W(1,2), W(2,2)) is outer-approximated by support-function
   SDPs in a fixed set of directions (the 3 axes plus 10 mixed directions); chi(2) is bounded over that polytope. The naive interval
   propagation from the single bounds is reported as well.
3. Comparison with the measured string tension sigma a^2 = 0.1227 +- 0.0043 (beta = 2.3) and 0.0666 +- 0.0015 (beta = 2.4)
   (`results/ttl_summary.json`, squares of `a_sqrt_sigma`), and with the Monte Carlo chi(2), W(1,2), W(2,2) measured by
   `mc_reference.py` (12^4 at beta = 2.3, 14^4 at beta = 2.4). Expectation stated now: chi(2) is not sigma (it contains perimeter and
   Coulomb corrections), and at L_max <= 16 the chi(2) interval will be wide (KZ call their string tension "qualitative").
4. Towards the gap: rigorous upper bounds on the static potential V_0(R) <= -ln(W(R,T))/T from lower bounds on W(R,T) (transfer
   matrix positivity, overlap sum 1), and a statement of what positivity can and cannot bound from below (lower bounds on energies need
   input beyond any finite set of moments).

What is reproduction (the KZ method in 2D and 4D) and what, if anything, is new (singlet/adjoint split, exact-arithmetic certificates,
the energy statements) is said in the README.

## Result (2026-11-21, after the runs; nothing above changed)

- **(a) 2D: pass.** All intervals at L_max = 8, 12, 16 contain the exact u_P and u_P^(RT) for W(1,2), W(2,2), W(1,3) at
  beta = 1, 2, 4. Both floating and rigorous intervals pass. Plaquette widths at L_max = 16: 0.0031, 0.0145, 0.0233.
- **(b) 4D: pass.** The plaquette intervals at beta = 2.0, 2.3, 2.4, 2.5 and L_max = 8, 12, 16 (truncated) contain the Monte Carlo
  references. beta = 2.0 used the new CPU run: 0.50124(8) on 10^4. KZ overlap: yes at every comparable point. Our L_max = 16 interval
  [0.082, 0.681] (beta = 2.3) contains their L_max = 16 band and overlaps their L_max = 24 interval, but it is much wider, because
  our L_max = 16 uses truncated bases (2D length-8 lines).
- **(c) Widths:** 4D plaquette widths at L_max = 16 (truncated): 0.52 (beta = 2.0) to 0.65 (beta = 2.5).
- **Rigour:** every bound has an exact-arithmetic certificate. The rigorous bound is weaker by at most 4e-7 (small problems),
  2.4e-5 (2D L_max = 16), 1.6e-4 (4D L_max = 12) and 2.9e-4 (4D L_max = 16). **The 1e-5 target is missed for the three large
  problems**; the cause is in README section 4.
- **Exploratory:**
  - chi(2) polytope in 2D at L_max = 16: [0.130, 0.928] at beta = 2 (exact 0.837) and [0.166, 0.449] at beta = 4 (exact 0.418).
  - In 4D only the naive interval was computed, about [-9, 11]: uninformative. **Deviation:** the 4D polytope was not run, because
    it costs about 2 h per beta and cannot fix a W(2,2) lower bound of 1e-4.
  - Monte Carlo chi(2) = 0.318 (beta = 2.3) and 0.254 (beta = 2.4), against sigma a^2 = 0.123 and 0.067.
  - Static potential: rigorous upper bounds only (README section 6).
- **Verdict: validated.** No interval missed its reference. Details: `README.md`, `results/bootstrap_summary.json`.
