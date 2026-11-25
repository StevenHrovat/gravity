# Positivity bootstrap for SU(2) lattice Yang-Mills

**What this is.** A program that bounds expectation values of SU(2) lattice Yang-Mills from two consistency conditions, with no
simulation. Every bound printed here holds for the true values (it is a theorem about the Wilson-action measure), and the main ones are
checked in exact integer arithmetic. The two conditions:
- **Loop equations:** the Schwinger-Dyson identities, i.e. gauge invariance of the measure under a change of one link variable.
- **Positivity:** Hermitian (Gram) positivity and reflection positivity, the physics reading of DMP's "two witnesses".

Method after Kazakov and Zheng (KZ, arXiv:2404.16925). The code is written from scratch here; no published code was used.
Pre-registration: [`PREREG-BOOTSTRAP.md`](PREREG-BOOTSTRAP.md), written before any bound was computed.

**Short answer.**
- 2D: the bounds contain the exact answers at every point (pre-registered check passed). At L_max = 16 the plaquette window is
  1.3 % (beta = 1), 3.3 % (beta = 2) and 3.5 % (beta = 4) of the exact value wide. L_max = 20 was pre-registered "if cheap" and was
  not run.
- 4D: the bounds contain this project's Monte Carlo plaquettes at beta = 2.0, 2.3, 2.4, 2.5 (pre-registered check passed). With the
  loop lengths this laptop can reach (L_max = 16 with truncated bases), the bounds are wide:
  plaquette in [0.082, 0.681] at beta = 2.3 (Monte Carlo 0.6022), [0.070, 0.694] at 2.4, [0.058, 0.706] at 2.5, [0.113, 0.635] at 2.0 (L_max = 16, truncated).
  KZ's L_max = 16 band (about [0.48, 0.66] at beta = 2.3) is tighter because they use the full 4D basis of length-8 lines. That
  basis needs more memory and a smarter build than this laptop allows. KZ's L_max = 24 run took 1 TB and 20 days.
- Rigour: every reported bound comes with a dual certificate checked in exact integer arithmetic. The rigorous numbers are weaker
  than the floating ones by at most 3e-4 (4D L_max = 16), 2e-5 (2D L_max = 16), below 1e-6 for the small problems.
- String tension and gap: at these cutoffs the Creutz ratio chi(2) is not bounded usefully. Positivity gives rigorous **upper**
  bounds on energies (static potential). Upper bounds can never certify a gap; a gap needs a lower bound, and a lower bound needs
  more than any finite set of consistency conditions supplies (section 6).

## 1. What was computed

| file | what |
|---|---|
| `su2boot.py` | paths, loop canonical form (translations, hypercubic group, rotation, reversal, free reduction), the SU(2) loop equations, positivity families, symmetry block-diagonalisation |
| `su2sdp.py` | SDP assembly, Clarabel solve, exact-arithmetic certificate |
| `run_bootstrap.py` | lower and upper bounds for a list of beta and loops, floating and rigorous; writes `results/bootstrap_d{d}_L{L}.json` |
| `check_equations.py` | checks the loop equations against Monte Carlo configurations (`results/bootstrap_eqcheck_d{2,4}.json`) |
| `mc_reference.py` | CPU Monte Carlo in any dimension for reference values (`results/bootstrap_mc_reference.json`) |
| `creutz.py` | exploratory: Creutz-ratio bounds from certified support values (`results/bootstrap_creutz_*.json`) |
| `summarize.py` | applies the pre-registered checks, prints the tables, static-potential bounds (`results/bootstrap_summary.json`) |

**Variables:** one per loop class, w(C) = <(1/2) tr U_C>; the class is taken modulo translations, the hypercubic group, cyclic
rotation, orientation reversal and free reduction. Wilson action S = -(beta/2) sum_p tr U_p.

**Loop equations:** for a closed path W based at a site and one of the 2d links V leaving that site, the Schwinger-Dyson identity is
closed on single traces with the SU(2) Fierz and Mandelstam identities (tr A tr B = tr AB + tr AB^-1):

    sum_{W = A V B} [ t(W)/4 + t(A (VB)^-1)/2 ] - sum_{W = A V^-1 B} [ t(W)/4 + t(A V^-1 B^-1)/2 ]
      + (beta/8) sum_{staples S of V} [ t(W V S) - t(W S^-1 V^-1) ] = 0

W runs over all reduced closed paths at the origin up to W_max (tails allowed; V = +e1 suffices by symmetry). This is the complete
single-trace family: it includes the Makeenko-Migdal equations (V on W) and the "backtrack" equations (V not on W).
- **Check:** on Monte Carlo configurations the residuals vanish within errors. 2D: 48 equations, rms z = 1.22. 4D: 17 equations,
  rms z = 1.05 with 4000 measurements.
- **Lesson:** a loop that appears in only one equation must not be dropped. Its |w| <= 1 bound makes the equation informative; in
  2D this is what gives a lower bound at all.

**Positivity:** basis = closed paths A_i at the origin (Wilson lines that start and end there, tails allowed). For SU(2) the Gram
matrix of the matrix elements of the A_i splits exactly into a singlet and an adjoint channel. Both are imposed: M + N >= 0 and
M - N >= 0, with M_ij = w(A_i^-1 A_j) and N_ij = w(A_i A_j) (KZ impose M >= 0, the sum of the two). The same split applies to:
- site reflection (x1 -> -x1),
- diagonal reflection (x1 <-> x2),
- link reflection (x1 -> 1 - x1, crossing links gauge-fixed).

Each matrix is block-diagonalised numerically with its symmetry group: 768 elements for the 4D Gram matrix, so 1249 x 1249 becomes
blocks of at most 37.

**SDP:** Clarabel 0.11 (interior point), called directly rather than through cvxpy so that the dual is under control. cvxpy is
installed but not used. Box |w| <= 1 on every variable.

**Certificate (rigour):** the solver's dual is turned into a proof by these steps:
1. Take the solver's dual (y for the equations, Z_k >= 0 for the blocks).
2. Rebuild each Z in the **unreduced** basis as R R^T, with R the dyadic rounding of E_k L_k. It is exactly PSD by construction,
   so the floating symmetry reduction plays no role in the proof.
3. Refine y by least squares and round it to dyadic rationals.
4. Take beta as an exact decimal rational.
5. Evaluate the bound b.y - <Z, F_0> - ||rho||_1 exactly; rho is the stationarity residual, covered by |w| <= 1. The Gram matrix
   R R^T is computed exactly as integer limbs: 21-bit limbs in float64 BLAS, with every partial sum below 2^53, so it is exact.
   Class sums are in int64, the rest in Python integers and fractions.

Weak duality then gives a bound valid for every point satisfying the constraints, so for the true values.

## 2. Validation against the pre-registered criteria

**(a) 2D, exact answers u = I2(beta)/I1(beta), W(R,T) = u^(RT): passed at every point and every L_max** (`results/bootstrap_d2_L*.json`).

| beta | loop | exact | L_max = 8 | L_max = 12 | L_max = 16 (rigorous) |
|---|---|---|---|---|---|
| 1 | W(1,1) | 0.240194 | [0, 0.380199] | [0.224371, 0.286139] | [0.238513, 0.241618] |
| 1 | W(1,2) | 0.057693 | [0, 1] | [0.050387, 0.130896] | [0.056886, 0.062135] |
| 1 | W(2,2) | 0.003328 | not in set | [0.002540, 0.522008] | [0.003230, 0.017049] |
| 1 | W(1,3) | 0.013858 | not in set | [-0.119110, 0.180748] | [0.009507, 0.022123] |
| 2 | W(1,1) | 0.433127 | [0, 0.584847] | [0.383773, 0.509762] | [0.425382, 0.439903] |
| 2 | W(1,2) | 0.187599 | [0, 1] | [0.147700, 0.308610] | [0.180947, 0.202581] |
| 2 | W(2,2) | 0.035194 | not in set | [0.021883, 0.794134] | [0.032732, 0.078441] |
| 2 | W(1,3) | 0.081254 | not in set | [-0.085774, 0.298200] | [0.072192, 0.107113] |
| 4 | W(1,1) | 0.658047 | [0, 0.757548] | [0.493892, 0.706217] | [0.643379, 0.666709] |
| 4 | W(1,2) | 0.433026 | [0, 1] | [0.247479, 0.540392] | [0.413955, 0.456024] |
| 4 | W(2,2) | 0.187512 | not in set | [0.062500, 0.754423] | [0.171348, 0.253293] |
| 4 | W(1,3) | 0.284952 | not in set | [-0.001210, 0.472808] | [0.264497, 0.325383] |

(L_max = 8 and 12: floating and rigorous agree to 1e-6. "not in set": the loop is longer than the cutoff can constrain, so the
bound is [-1, 1]. Every interval contains the exact value. Full tables with floating and rigorous columns:
`results/bootstrap_summary.json`.)

At L_max = 8 the upper bound 0.757548 at beta = 4 (lambda = 2) reproduces KZ's lowest-level 2D number (0.75755) exactly. The lower bound
appears first at L_max = 12. Widths at L_max = 16: plaquette 1.3 % (beta = 1), 3.3 % (beta = 2), 3.5 % (beta = 4) of the exact value.

**(b) 4D, plaquette against Monte Carlo (within 2 standard errors): passed at every beta and every L_max.**
References as pre-registered:
- beta = 2.3: 0.60224(6), `results/lattice_summary.json`.
- beta = 2.4: 0.630002(13), `lattice/runs-gpu/ttl_b2.4_L16.npz`.
- beta = 2.5: 0.651964(6), `lattice/runs-gpu/ttl_b2.5_L20.npz`.
- beta = 2.0: 0.50124(8), new CPU run, `mc_reference.py`, 10^4; 0.50118(15) on 8^4. That run finished before any 4D bound at
  beta = 2.0 was computed.

The CPU code reproduces the stored plaquettes (beta = 2.3: 0.60231(7); beta = 2.4: 0.62994(6)) and the exact 2D value
(0.43324(14) against 0.433127).

Plaquette u_P = W(1,1), rigorous bounds:

| beta | Monte Carlo | L_max = 8 | L_max = 12 | L_max = 16 (truncated) | contained |
|---|---|---|---|---|---|
| 2.0 | 0.50124(8) | [0, 0.804896] | [0, 0.635188] | [0.113420, 0.635155] | yes |
| 2.3 | 0.60224(6) | [0, 0.827713] | [0, 0.681000] | [0.081981, 0.681016] | yes |
| 2.4 | 0.630002(13) | [0, 0.834188] | [0, 0.693937] | [0.070340, 0.693985] | yes |
| 2.5 | 0.651964(6) | [0, 0.840197] | [0, 0.705782] | [0.058434, 0.706003] | yes |

(The lower bounds printed as 0 are between -1e-5 and 0 in the rigorous column.)

Larger loops at L_max = 16 (truncated), rigorous, against the new Monte Carlo (12^4 at beta = 2.3, 14^4 at 2.4, 10^4 at 2.0):

| beta | W(1,2) bounds | MC | W(2,2) bounds | MC | W(1,3) bounds | MC |
|---|---|---|---|---|---|---|
| 2.0 | [0.0136, 0.4627] | 0.2590 | [0.0001, 0.6959] | 0.0735 | [-0.0377, 0.3525] | 0.1346 |
| 2.3 | [0.0077, 0.5210] | 0.3859 | [0.0001, 0.7051] | 0.1799 | [-0.0465, 0.4122] | 0.2507 |
| 2.4 | [0.0059, 0.5380] | 0.4250 | [0.0000, 0.7075] | 0.2224 | [-0.0495, 0.4300] | 0.2912 |
| 2.5 | [0.0042, 0.5538] | none | [-0.0000, 0.7097] | none | [-0.0524, 0.4468] | none |

All contain the Monte Carlo values.

**Agreement with KZ** (their Fig. 1b, read off the plot to about +-0.01):
- Our L_max = 8 upper bound at beta = 2.3 (0.828) lies on their grey L_max <= 8 boundary (about 0.825 by extrapolating the plotted line).
- At L_max = 16 our interval [0.082, 0.681] contains their band [0.48, 0.66] and overlaps their L_max = 24 interval [0.549, 0.623]. That is
  consistent (both are rigorous) but **much wider**: ours is not "narrower than KZ", it is a truncated version of their L_max = 16.

**(c) Widths:** in the tables (column "width").

**Verdict (pre-registered): validated.** No interval missed its reference.

## 3. 4D results and how far the laptop got

| setting | variables | equations | PSD blocks (max size) | wall time (4 beta x 4 loops x 2 bounds) |
|---|---|---|---|---|
| L_max = 8, l_pos = 4 | 11 | 2 | 73 (4) | 1 s |
| L_max = 12, l_pos = 6 (complete) | 2480 | 529 | 162 (37) | 22 min, 8 processes |
| L_max = 16, truncated | 35493 | 9904 | 206 (46) | 66 min, 3 processes |

**L_max = 16, truncated** (`results/bootstrap_d4_L16_trunc.json`, settings recorded there):
- Positivity: all four families with the complete 4D basis of length <= 6, plus all four with length-8 paths restricted to one plane.
- Loop equations: from every path of length <= 8 in 4D, every path of length <= 12 in a plane, and every path of length <= 10 in a
  3D sublattice. Staples always run in all four directions.
- This is the "dimensional truncation" allowed in the pre-registration. It is weaker than KZ's L_max = 16, which uses the full 4D
  set of level-2 lines.

**What limits it** (measured):
- The complete 4D basis of length 8 has 37,681 paths per site, so its key matrix would have 1.4e9 entries.
- A KZ-like basis (all length <= 6 plus products of two length-4 paths, 3265 paths for the Gram family) built in 20 minutes. Its
  SDP needed more than 12 GB per solver process and ran the laptop out of memory, so it was stopped.
- The truncated L_max = 16 solves in about 5 minutes per bound at about 7 GB.
- Going from L_max = 12 to the truncated 16 created a lower bound (0 -> 0.08 at beta = 2.3) but left the upper bound unchanged
  (0.681). The upper bound is set by the 4D length-6 basis. Moving it needs the full length-8 4D lines, i.e. a bigger machine and a
  smarter build (enumeration modulo symmetry, compiled canonicalisation).

## 4. Rigour status

Every bound in the tables has a rigorous twin from an exact-arithmetic certificate (method in section 1). The final number is an
exact rational, stored in the JSON when short.

| run | largest gap floating -> rigorous | solver status |
|---|---|---|
| 2D L_max = 8, 12; 4D L_max = 8 | < 4e-7 | Solved / AlmostSolved |
| 2D L_max = 16 | 2.4e-5 | AlmostSolved / NumericalError |
| 4D L_max = 12 | 1.6e-4 | AlmostSolved / NumericalError |
| 4D L_max = 16 (truncated) | 2.9e-4 | NumericalError |

- The pre-registered target (rigorous weaker by at most 1e-5) is **met for the small problems and missed for the large ones**
  (up to 3e-4). The cause: Clarabel stops at its precision limit ("NumericalError" with tolerance 1e-10). Its last dual is still a
  good certificate, but its stationarity residual is about 1e-8 per variable over 35,000 variables, and the certificate absorbs
  that residual through |w| <= 1, which costs ||rho||_1.
- The loss is three orders of magnitude below the widths, so it changes no conclusion.
- A solver status of "NumericalError" does not weaken the rigour: the certificate is checked independently of the solver.
- What the rigour rests on:
  1. the loop equations and positivity conditions being true for the Wilson measure (theorems; the equations are also checked
     numerically, section 1);
  2. |w(C)| <= 1;
  3. the code that enumerates the constraints (tested by the 2D exact check and the Monte Carlo residual checks, not formally
     verified).

  The exact arithmetic removes floating-point error from the SDP side; it does not verify the constraint generator.

## 5. Exploratory: Creutz ratio and string tension (labelled exploratory in the pre-registration)

Creutz ratio chi(2) = -ln[W(2,2) W(1,1) / W(1,2)^2], rigorous intervals:

| case | naive (from single bounds) | polytope (13 directions, 26 certified SDPs) | exact / Monte Carlo |
|---|---|---|---|
| 2D, beta = 2, L_max = 16 | [-0.052, 1.081] | [0.130, 0.928] | 0.8367 (exact, = -ln u) |
| 2D, beta = 4, L_max = 16 | [0.015, 0.635] | [0.166, 0.449] | 0.4180 (exact) |
| 4D, beta = 2.3, L_max = 16 | [-9.0, 11.0] | not run (see below) | MC 0.3180(3); sigma a^2 = 0.1227(43) |
| 4D, beta = 2.4, L_max = 16 | [-9.6, 12.2] | not run | MC 0.2541(2); sigma a^2 = 0.0666(15) |

- **2D:** consistency alone certifies a strictly positive Creutz ratio, chi(2) >= 0.13 at beta = 2 and >= 0.17 at beta = 4. The
  true values are 0.84 and 0.42. In 2D the area law is exact, so this is a check, not news.
- **4D:** at the reachable cutoffs W(2,2) is only bounded below by about 1e-4, so the interval says nothing about the string tension.
- **Deviation from the pre-registration, stated plainly:** the pre-registered polytope (26 SDPs per beta) was run in 2D but not in
  4D. Each 4D L_max = 16 SDP takes about 5 minutes at 7 GB, so the polytope would take about 2 hours per beta. It cannot repair a
  W(2,2) lower bound of 1e-4: the upper end of chi(2) stays above 9.
- The Monte Carlo Creutz ratios (0.318 and 0.254) are 2.6 and 3.8 times sigma a^2, as expected at R = 2 (perimeter and Coulomb
  terms; pre-registered expectation).

## 6. Towards the gap: what consistency alone can and cannot bound

**What was computed: rigorous upper bounds on the static potential** (`summarize.py`, section "V0"). In temporal gauge,
W(R,T) = sum_n c_n exp(-V_n(R) T). The c_n are >= 0 by reflection positivity and sum to 1, since W(R,0) = 1. Hence:
- W(R,T) <= exp(-V_0 T), so V_0(R) <= -ln(W_lo(R,T)) / T;
- W(R,T+1) / W(R,T) <= exp(-V_0), so V_0(R) <= ln(W_up(R,T) / W_lo(R,T+1)).
Both use only certified bounds.

| case | rigorous upper bound on V_0(1) | value |
|---|---|---|
| 2D beta = 1, L_max = 16 | 1.433 | exact -ln u = 1.426 |
| 2D beta = 4, L_max = 16 | 0.441 | exact 0.418 |
| 4D beta = 2.3, L_max = 16 trunc | 2.43 | MC estimate -ln(W(1,3)/W(1,2)) = 0.43 |

In 2D the bound is within 0.5 % (beta = 1) and 6 % (beta = 4) of the truth. In 4D it is valid but loose.

**What cannot be computed this way.** Every such statement is an **upper** bound on an energy, because positivity says how cheap a
state *can* be made, not how expensive every state *must* be. Formally, the correlator of any reflection-positive operator is a
moment sequence C(t) = sum_n c_n x_n^t with x_n = exp(-E_n) in [0, 1]. Given finitely many moments, one can always add a tiny
weight close to x = 1 (an arbitrarily light state with an arbitrarily small overlap) without violating any positivity condition.
Hence:
- No finite set of consistency conditions bounds the lightest energy from below. The gap is exactly such a lower bound.
- The glueball channel needs correlators of two separated loops, i.e. **double-trace** variables. These are not part of the
  single-trace SU(2) system (KZ's closure), so even the upper bound on the glueball mass is out of reach without extending the
  variable set (the SU(3) bootstrap arXiv:2502.14421 adds multi-trace operators).

A lower bound on the gap would need an extra input that is not a finite consistency check. Examples: a uniform bound on how the
moments decay (a cluster property at a finite rate, which is the gap itself), or an analytic argument controlling all loop lengths
at once. This is the same structure as in section 3.1b of the mass-gap README: the reach postulate is the gap.

## 7. Reproduction and what is new

- **Reproduction:** the KZ method (single-trace SU(2) loop equations, Hermitian and reflection positivity, symmetry reduction) in 2D
  and 4D. The 2D results and the 4D L_max = 8 number agree with theirs where they can be compared.
- **Not reached:** KZ's 4D L_max = 16 and 24 widths. Their L_max = 24 needed 1 TB of memory; our L_max = 16 uses truncated bases.
- **New, modest:**
  1. The singlet/adjoint split of the SU(2) Gram and reflection matrices (M +- N >= 0, the full matrix-element positivity). It is
     stronger than tr-positivity; I have not found it stated for SU(2) in KZ.
  2. Exact-arithmetic verification of every reported bound. KZ report floating SDP results.
  3. The static-potential upper bounds of section 6 as an explicit rigorous statement.
  None of these is a physics result beyond the bounds themselves.

## 8. The DMP reading (one paragraph)

The owner's reading is that a complete system "certifies its existence by consistency alone". The bootstrap shows what consistency
alone does for Yang-Mills on the lattice:
- It certifies **bounds**. With nothing but gauge invariance (the loop equations) and the two witnesses (reflection positivity), the
  plaquette is confined to a window that contains the simulated value. In 2D that window closes onto the exact answer as the cutoff
  grows.
- It does not certify a **gap**. Positivity bounds energies from above (a state is at most as expensive as the cheapest trial
  certificate), never from below. A floor on the cost of existence needs an input that no finite set of consistency checks supplies.
  This is the same place where section 3.1b of the mass-gap README locates the open problem (the reach postulate).

So the bootstrap is the physics method closest to "existence by consistency". On this laptop it certifies the vacuum's observables
within a window, and it says precisely that the gap would need more than that.

## 9. Runtime, how to re-run, what remains

**Runtime on this laptop** (CPU only; the GPU was not used, CUDA_VISIBLE_DEVICES = -1 in every script):
- 2D L_max = 16: 10 minutes.
- 4D L_max = 12: 22 minutes.
- 4D L_max = 16 (truncated): 66 minutes.
- 2D Creutz polytope: 60 minutes.
- Monte Carlo references: up to 1.9 hours, in parallel with the above.
- Equation checks: 4 minutes.
- Peak memory: about 7 GB per 4D L_max = 16 solver process. The loop-equation and family builds are cached in `$SU2BOOT_CACHE`
  (default `%TEMP%/su2boot_cache`).

**Re-run** (from `docs/mass-gap/`):

    py bootstrap/check_equations.py 2 24 2.0 3000 8        # loop equations vs Monte Carlo, 2D
    py bootstrap/check_equations.py 4 4 2.3 4000 6         # ... 4D
    py bootstrap/mc_reference.py                           # Monte Carlo references (about 2 h)
    py bootstrap/run_bootstrap.py --d 2 --Lmax 16 --betas 1,2,4 --targets 1x1,1x2,2x2,1x3 --procs 10
    py bootstrap/run_bootstrap.py --d 4 --Lmax 12 --betas 2.0,2.3,2.4,2.5 --targets 1x1,1x2,2x2,1x3 --procs 8
    py bootstrap/run_bootstrap.py --d 4 --Lmax 16 --lpos 6 --Wmax 8 --extra-fams G:8:2,RS:8:2,RD:8:2,RL:8:2 --extra-eqs 12:2,10:3 --betas 2.0,2.3,2.4,2.5 --targets 1x1,1x2,2x2,1x3 --procs 3 --tag trunc
    py bootstrap/creutz.py --d 2 --Lmax 16 --betas 2,4 --procs 3
    py bootstrap/summarize.py bootstrap_d2_L8.json bootstrap_d2_L12.json bootstrap_d2_L16.json bootstrap_d4_L8.json bootstrap_d4_L12.json bootstrap_d4_L16_trunc.json

**What remains:**
1. **Full 4D L_max = 16**, to reach KZ's band and go beyond it. This needs:
   - enumeration of paths and equations modulo the symmetry group (orbit representatives only);
   - a compiled or vectorised canonical form;
   - block construction from group projectors instead of dense averaging;
   - a bigger machine. Estimated 20 to 60 GB and an hour or two per beta, not measured.
2. **Tighter certificates:** a final solver polish (or an exact projection of y onto the equation range) would bring the rigour
   loss below 1e-5.
3. **Double-trace variables** (as in the SU(3) bootstrap), the only route inside this framework to glueball correlators. Even then,
   only upper bounds on masses follow (section 6).
4. A literature check that the singlet/adjoint split is not already in KZ's SU(2) implementation. Their text speaks of tr-positivity.
