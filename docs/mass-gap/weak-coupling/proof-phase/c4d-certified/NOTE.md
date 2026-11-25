# Cycle 4, workstream 4 (c4d): the measured point's W1 column, certified (2026-11-22)

Brief: turn the GPU refit's one passing point (beta = 2.3, b = 8, L sqrt(sigma) = 2.80) into a certified statement: certify (or refute)
the W1 Dobrushin condition, centre half included, for the blocked action actually measured. Pre-registration: `PREREG.md` (written before
any certified run). Marks as in `../c3c-certified/NOTE.md`: **Lean** (machine-checked), **paper** (complete argument here), **certified**
(interval arithmetic with outward rounding, every cell of the parameter domain enclosed, not a scan), **numerical**, **conjecture**.

Files: `check_structure.py` (neighbour structure), `check_formulas.py` (closed forms against quadrature on S^3), `check_enclosure.py`
(interval enclosures against 50-digit Bessel functions: 4500 checks, 0 failures), `cert_measured.py` + `cert_measured.json`/`.log` (the
certificate), `fine.py/.json/.log` (cell-resolution dependence), `margin.py/.json/.log` (margins and budgets), `iso_window.py/.json/.log`
(task 2 by-product); Lean `../../../formal/ProofPhase/Certified/Measured.lean`, built in `~/formal-c4d` (`setup-c4d.sh`, `build-c4d.sh`,
`axioms-c4d.sh`). All runs CPU, `CUDA_VISIBLE_DEVICES=-1`, one process, the certificate takes 26 s (every run far below 30 min). No GPU job
was rerun and no committed refit result was touched.

**Claim discipline, first.** Everything below is a statement about the **fitted, truncated, anisotropic effective action** on the coarse
torus (SU(2) links, 4D), at the fitted couplings and a box around them. It is *not* a statement about lattice Yang-Mills, not about the
true blocked action (distance: `H1LocalLip`, truncation, closure), and `ObsTransferPhys` is untouched. "Certified < 1" means: that action
satisfies the W1 form of D' (Lean: `LimitDprimeW`), no more.

---

## 0. Results at a glance

1. **The linearised 0.676 was not misleading: the nonlinear certified column is below 1 for the base fit and for every extension.**
   Certified upper bound on the full W1 column (both halves, nonlinear, sup over all conditional laws), spatial links (the binding type;
   temporal 0.30 to 0.56), box = +-3 sigma of all four fits (rounded up), 1/400 cells; numbers from `cert_measured.log`:

   | fit | linearised H_W (cycle 3, central) | **certified column, box** | certified column, central couplings | largest certified common scale of the box |
   |---|---|---|---|---|
   | base (b_F, b_A) | 0.676 | **0.7318** | 0.7137 | 1.34 |
   | ext_T (+ spin 3/2) | about 0.68 | **0.7611** | 0.7215 | 1.28 |
   | ext_R (+ 1x2 rectangle, b_R = 0.0084) | about 0.89 | **0.9640** | 0.9380 | 1.035 |
   | ext_TR (both) | about 0.89 | **0.99988** (1.00015 at 1/200 cells; 0.99974 at 1/1600) | 0.9475 | 0.9997 |

   Reading: outcome 1 of PREREG (certified < 1 over the box) for all four fits; outcome 2 (certified >= 1) cannot occur here (stated before
   the run: this method gives only upper bounds); **ext_TR over the box is on the knife edge** (margin 0.0001, resolution dependent) and
   should be read as "inconclusive over the box, certified at the central couplings (0.948)". The Lean statement covers the base fit and
   ext_T (plaquettes only): `Kmeas = 0.05442`, uniform column `18 Kmeas = 0.9796` (class-resolved column 0.761, note below).
2. **The binding half is the centre (fundamental) half**, as the refit said: base spatial column = fundamental 0.711 + adjoint 0.021
   (box). The adjoint half (b_A about 10^-3) is two orders below its window.
3. **Where the nonlinear constant comes from.** Per unit of fundamental coupling the certified constant is `N_F* = 0.2967` (base box),
   against 0.2829 = 8/(9 pi) at the uniform law (linearised) and 0.2887 = sqrt(1/12) (the Hodge-bound at the uniform law): so the
   nonlinearity costs only about 4 % over the linearised column (0.2943 central), the rest is the H^-1 relaxation (2 %) and the
   perturbation by the adjoint/cubic couplings (3 %). The conditional laws are *not* near-uniform (|A| up to 0.8, zeta up to 1.16) yet the
   column barely moves: the degree-1 structure of the derivative measure `(<u,b> - m) rho` dominates.
4. **Large closure residuals (caveat 3) do change the margin, not (yet) the sign.** Adding the unfitted 1x2 rectangle (closure6 = -0.67)
   costs +0.23 of column (0.76 -> 0.96): from a margin of 0.27 to 0.036 (box) / 0.062 (central). Any further centre-charged loop family
   of the same size (90 neighbour incidences per link, e.g. 1x3, 2x2, bent loops) with coupling above `0.0013` (box) / `0.0023` (central)
   makes the certified column exceed 1 (`margin.log`, budget column). Since closure6 reached 67 % for the base fit, the fit has no
   demonstrated convergence in the loop expansion: the verdict is **not robust to further truncation levels**, and NOT_EXCLUDED
   stays biased towards false positives. What *is* shown: truncating at plaquettes (+ spin 3/2) or at plaquettes + rectangles, the
   fitted action is inside the W1 window.
5. **Neighbour structure (task 1, first item): `analyse_refit.py` and `AdjointW.lean` agree** (`check_structure.py`): every link `i != z`
   shares at most one plaquette with `z`; a temporal link lies in 6 ts plaquettes, a spatial link in 2 ts + 4 ss (`PLAQ_PER_LINK`); the
   Lean `common i z` counts shared plaquettes (sum <= 18); the pair table's rows sum to 18/0 (t) and 6/12 (s) plaquette incidences plus 90
   rectangle incidences. Differences, both on the Lean side: one coefficient for all plaquettes (no ts/ss split), and no rectangles.
   Neither affects correctness; `Measured.lean` keeps the uniform constant (sound, 18 Kmeas = 0.980 instead of 0.761).
6. **Isotropic window (task 2, only the beta_F direction; the beta_A ceiling is untouched).** The new fundamental-channel bound replaces
   c3c's crude `e^a` bound: at beta_A = 0 the certified |beta_F| window grows from 0.0685 to **0.1924** (linearised limit 0.1964; factor
   2.8), at |beta_A| <= 0.01 to 0.1369, at 0.02 to 0.0892 (`iso_window.log`; corners (|b_A|, |b_F|): (0, 0.1924), (0.002, 0.1806),
   (0.005, 0.1637), (0.01, 0.1369), (0.02, 0.0892), (0.03, 0.0458)). Beyond |b_A| about 0.03 the new perturbation treatment is worse than
   c3c's Bingham corners, so the union is the window. **Not done:** the beta_A ceiling (0.21 -> 0.275), see section 7.
7. **Lean:** `Measured.lean` builds clean (no sorry, no native_decide, no new axiom, no warnings; axioms of all headline theorems:
   `propext, Classical.choice, Quot.sound`). One named hypothesis `CertifiedMeasured`; `kMeas_column_lt_one : 18 * Kmeas < 1` by `norm_num`.

**Amendments after the first run (honesty; all before any result was accepted).** The first run of `cert_measured.py` used the crude
treatment of the centre-blind and cubic terms of PREREG (`N_h`, `N_g` by the plain L^2 bound, columns base 0.763, ext_T 0.815, ext_R 0.9935,
ext_TR 1.052), took the maximum over the direction endpoints of the *sum* main + perturbation (not valid for a concave bound: replaced by the sum of the
maxima), and its series tail bound was valid only for y <= 1.1 (the x1.5 and x2 scales; replaced by a bound valid for any y). The refined
treatment (v) of section 1 was added after seeing that ext_TR was above 1 with a crude term; it only affects the small terms (`N_h`, `N_g`), not the
fundamental channel. The numbers reported are from the final code (rerun in full). PREREG.md's method paragraph describes the first version;
section 1 here is the final one.

## 1. The object and the reduction (paper)

Link `i` (temporal or spatial). Single-link conditional density w.r.t. Haar on S^3 = SU(2): `rho_i ~ exp(<A,u> + Psi(u))`, with
`A = sum_p bF(p) s_p + sum_R bR s_R` (unit-quaternion staples; fundamental parts of plaquettes and rectangles) and
`Psi = sum_p [(bA(p)/3)(4 t_p^2 - 1) + bT(p)(2 t_p^3 - t_p)]`, `t_p = <u, s_p>`. Moving a neighbour `z` which shares the factor `f`
with `i` by geodesic distance `d` moves `s_f` at unit speed (left/right translation is an isometry), the derivative of the law is
`(F - E F) rho`, `F = phi_f'(<u,s_f>) <u,b>` (b unit, b perp s_f; relaxed to any unit b), and as in c3c (Sec. 3.1) the influence is
at most `sum_{f ni i,z} N_f` with `N_f = sup ||(F - EF) rho||_KR`. The column of `z` is `sum_f (number of other links of f) N_f`: plaquettes
3, rectangles 5. `phi_f' = bF + (8 bA/3) t + bT (6 t^2 - 1)` splits `F` into `bF f + (8 bA/3) h + bT g`, with `f = <u,b>`,
`h = <u,a><u,b>` (`|h| <= 1/2`), `g = (6 t^2 - 1)<u,b>` (`|g| <= (10/3) sqrt(5/18) = 1.757`); triangle inequality in the KR norm.

**Tools (all elementary, paper):** (i) `||g Haar||_KR <= ||g||_{H^-1}` for mean-zero g (|grad phi| <= 1, Cauchy-Schwarz); (ii) degree split:
Laplace eigenvalues `l(l+2)` = 3 (degree 1), >= 8 above, so `||g||_{H^-1}^2 <= ||g_1||^2/3 + (||g||^2 - ||g_1||^2)/8`, `||g_1||^2 = 4 |Cov_rho(f,u)|^2`;
(iii) Bessel closed forms for `rho_A ~ exp(<A,u>)`, `|A| = r`, with `y = r^2/4`, `S_nu(y) = sum y^k/(k!(k+nu)!)`, `Z(r) = S_1(y)`,
`x(r) = E cos t = I_2/I_1`, `q(r) = E cos^2 t = 1 - 3 I_2/(r I_1)`, `zeta = Z(2r)/Z(r)^2 = ||rho_A||_2^2`; the quantities
`||g||^2 = zeta V` and `||g_1||^2` are *linear in c^2* (c = cosine of the angle between A and b), so the direction sup is at c^2 in {0,1};
checked against quadrature to 4e-14 (`check_formulas.py`); (iv) perturbation: `rho = rho_A w / E w`, `osc Psi <= Dq := sum_p (4|bA|/3 + 2|bT|)`
gives `|rho/rho_A - 1| <= eps = e^{Dq} - 1` and `||g' - g||_{H^-1} <= eps (sqrt(zeta V) + E|f|(1+eps) sqrt(zeta))/sqrt 3`;
(v) for the centre-blind and cubic terms (reference `h`, `g` have H^-1 norms `sqrt(1/192)` and `sqrt(0.3125/15)` at the uniform law):
`N <= ||ref||_{H^-1} + (sup|G - c|) sqrt(zeta_eff - 1)/sqrt 3`, `c = E_rho G`, `zeta_eff = (1+eps)^2 zeta*` (decomposition
`(G - c) rho = G + [(G - c)(rho - 1) - c]`, the bracket has mean zero).
`N_F* = sup_{r <= a}` (a = max over link types of the sum of |fundamental couplings| through a link, rectangles included). Monotone in
all coupling bounds, so the corner of the box covers the box. Interval arithmetic: mpmath `iv`, 100 bit, power series with nonnegative
terms and an explicit geometric tail bound, 1/400 cells of r (`check_enclosure.py`).

**Marks:** the reduction, the closed forms and the bound `N_F*`: paper + certified (substantive; c3c had only a crude `e^a` bound in the
fundamental channel, which would have given a spurious 2.7). The corner arithmetic and `norm_num` steps: definitional.

## 2. Results (details)

`cert_measured.log` (base, spatial column; `fund` / `adj` / `cubic` are the three parts of the spatial column, box x1.0):

| fit | fund | adj | cubic | column (spatial) | temporal | N_F* | zeta* | Dq |
|---|---|---|---|---|---|---|---|---|
| base | 0.7111 | 0.0208 | 0 | 0.7318 | 0.3045 | 0.29665 | 1.159 | 0.0136 |
| ext_T | 0.7266 | 0.0218 | 0.0127 | 0.7611 | 0.3242 | 0.30313 | 1.159 | 0.0244 |
| ext_R | 0.9407 | 0.0234 | 0 | 0.9640 | 0.5357 | 0.29665 | 1.225 | 0.0136 |
| ext_TR | 0.9612 | 0.0243 | 0.0143 | 0.99988 | 0.5621 | 0.30313 | 1.225 | 0.0244 |

Per-plaquette constants (ext_T box): `k_ts = 0.01801`, `k_ss = 0.05442`; rectangle (ext_R) `k_R = 0.00255`. Scaling the box
(x1.1, x1.25, x1.5, x2, `cert_measured.log`): base column 0.809, 0.925, 1.124, 1.534: the base fit would stay certified up to
all couplings 34 % larger. Cell-resolution dependence (`fine.log`): base 0.7324 / 0.7320 / 0.7318 / 0.7318 at 1/100, 1/200, 1/400, 1/1600;
ext_TR 1.0012 / 1.0002 / 0.9999 / 0.9997.

**Verdict for the measured point (task 1): CERTIFIED < 1** (nonlinear, sup over all conditional laws, both halves, ts and ss resolved,
box = +-3 sigma of all four fits): **0.7318 (base), 0.7611 (ext_T), 0.9640 (ext_R); ext_TR 0.99988 over the box, 0.9475 at the central
couplings.** Method: one-dimensional interval arithmetic over the field strength r in [0, a], a paper reduction to Bessel closed forms.

**What the verdict says and does not say.** The statistical errors are tiny (b_F ts 0.0540 +- 0.00012), so the box is a point for all
practical purposes; the systematic uncertainty of the fit (visible between base and ext_R: b_F ss 0.1711 vs 0.1700, i.e. 7 sigma) is inside
the box because the box contains every fit. Not covered: operators the fit does not contain (closure residuals, above); the fit's own
bias (SD fit on a 6^4 torus, one volume, one w = 2, one beta); the nonlinear coefficient is an **upper bound** (the true best constant
at the uniform law is 0.2829; the linearised column is a lower-type value 0.676 to 0.886).

## 3. Closure residuals and the verdict (task 1, last item)

Caveat 3 of the cycle-3 Result: closure4/5/6 of the base fit = -0.9 (+-0.4), -0.35 (+-0.13), -0.67 (+-0.001): the Schwinger-Dyson identities
of the unfitted spin-3/2 (ts, ss) and rectangle observables are off by 35 to 90 %. What each means for the column:

* spin 3/2 (closure4/5): the extension fit finds b_T = (-0.00009 +- 0.00025, 0.00033 +- 0.00018), consistent with zero; effect on the
  certified column +0.03 (the centre-blind and cubic couplings enter only through the crude-but-small terms). Can't change the verdict.
* rectangle (closure6): the fitted b_R = 0.0084 (200 sigma) is a real coupling and carries 90 neighbour incidences per link: +0.23 of column.
  The verdict remains certified < 1 but with a margin 0.036. **A further family of the same type could flip it** (budget 0.0013, box).
* Therefore: "the measured point is inside the W1 window" is certified for the actions *as fitted* (plaquette, plaquette + T, plaquette + R,
  plaquette + T + R); it is not a statement about the action with all loops, and the convergence of the loop sequence (0.73 -> 0.96 -> next?)
  is unknown. The honest summary: **the verdict survives the first truncation step; the second step would be decisive**
  (a refit with 1x3, 2x2 and the three bent loops, or with the correct infinite-dimensional treatment, e.g. a blocking whose action is
  closer to plaquette form: see section 6). That is a GPU/refit job (task not done here: no GPU rerun).

## 4. Lean (`formal/ProofPhase/Certified/Measured.lean`)

Built in `~/formal-c4d` against the current tree: no `sorry`, no `native_decide`, no new axioms, no warnings; axioms of the eight headline
theorems: `propext, Classical.choice, Quot.sound` (`axioms-c4d.sh`).

**The hypothesis, exactly.** `CertifiedMeasured : Prop`: for every torus `(Z/NZ)^4` with `N >= 2` and every coupling vector
`(Fts, Fss, Ats, Ass, Tts, Tss)` with `|Fts| <= 0.0545`, `|Fss| <= 0.1725`, `|Ats| <= 0.0011`, `|Ass| <= 0.0020`, `|Tts|, |Tss| <= 0.0009`
(`boxFts`, ..., the +-3 sigma box of the base fit and of ext_T, rounded up) and the action `measuredAction`
(time-like plaquettes `dir1 = 0` carry (Fts, Ats, Tts), space-like (Fss, Ass, Tss); factor `planeFactor = bF t + (bA/3)(4t^2 - 1) + bT(2 t^3 - t)`,
`t = 1/2 Re tr U_p`): `SiteInfluenceW (haarG SU2) plaqSupp (measuredAction ..) geodSU2 (fun i z => Kmeas * common i z)` with
`Kmeas = 5442/100000` (the certified `k_ss = 0.0544198`, rounded up; `k_ts = 0.0180` is below it). That is: for every Borel `F` reading only
link `i`, `L`-Lipschitz there for the geodesic cost, and every boundary configuration `sigma` and new value `s` at `z`:
`|int F dq^sigma - int F dq^{sigma[z -> s]}| <= Kmeas common(i,z) L geod(sigma_z, s)`.

**What is proved in Lean from it:**

| theorem | statement | mark |
|---|---|---|
| `abs_planeFactor_le`, `measurable_planeFactor`, `planeFactor_dep`, `potential_measuredAction` | the anisotropic action is a local potential (measurable, bounded by the sum of absolute couplings, reads only its plaquette) | elementary |
| `kMeas_column_lt_one` | `18 * Kmeas < 1` (= 0.97956) | `norm_num` (definitional arithmetic) |
| `measured_column_le`, `measured_dist_le` | column sum of `Kmeas * common` <= `18 Kmeas`; positive coefficients only between links of one plaquette (distance <= 1) | elementary (reuses `sum_common_le`) |
| **`limitDprimeW_measured`** | `CertifiedMeasured` => `LimitDprimeW (fun _ => measuredAction ..)` for every coupling vector in the box | composition; the content is the hypothesis |
| **`measured_decay`** | uniform-in-`N` exponential decay `|Cov(f,g)| <= pi (1 - 18 Kmeas e^lam)^-1 (sum v) L_g e^{-lam R}` for every action in the box, every `lam` with `18 Kmeas e^lam < 1` | composition |
| `exists_rate_measured` | such a `lam > 0` exists | elementary |

The hypothesis is the certified statement of sections 1-2 for the plaquette actions of the box (base and ext_T). Rectangles are not in the
Lean lattice structure (plaquette supports only): the ext_R / ext_TR numbers are paper + certified, not Lean. The class-resolved
column (0.761) would need the counting lemma "a spatial link lies in at most 4 space-like plaquettes" (a refinement of `card_slots03_le`,
`card_slots12_le`); not done, the uniform constant suffices for the < 1 statement.

## 5. Task 2 (isotropic window): what was done, what was not

The by-product (section 0, item 6) widens the beta_F direction of c3c's two-parameter window 2.8-fold at beta_A = 0 because c3c's fundamental bound
was crude, not because of anything new about the adjoint channel. The **beta_A direction (0.21 -> 0.275) is untouched**: c3c's NOTE puts
the slack in (i) the relaxation of the moved staple to all traceless matrices (constrained version about 0.235, float) and (ii) the triangle
inequality plus H^-1 for the deviation from the uniform point. The new technique (degree split, deviation measured in L^2 of `rho - 1`) does not
help there: at |b_A| = 0.2 the Bingham laws are far from uniform and `zeta` is large. The plan that would: certify the constrained bound by
adding the staple direction as extra cells near the vertex `s = (6,0,0,0)`, and use Theorem 2's exact transport for the Klein-symmetric part
(c3c section 9, items 1 and 2). Not attempted (this workstream's budget went into the measured point).

## 6. Task 3: design note for the non-blind smearing kernel (no code)

**Defect (c3a).** The block variable's staple kernel `1 + 2 w sum_nu cos k_nu` (transverse symbol) has zero or near-zero symbol at the spatial zone
corner at w = 1/2, 1 (checkerboard blindness), small w loses the content: a trade-off, no w is good in both respects.

**Design.** Replace the one-step staple sum by a **transverse heat kernel**: iterate n times a *small* positive one-step smearing
`K_0 = 1 + w_0 sum_staples` (spatial directions only, never crossing a time slice, so the reflection-positivity argument of `smearBlock`
carries over; SU(2) projection after each substep or once at the end, to be decided by the content check) with `w_0 < 1/6` (symbol
`1 + 2 w_0 sum cos k >= 1 - 6 w_0 > 0` on the whole zone; keep away from the Z2 tie weights 1/6, 1/4, 1/2), so that `K = K_0^n` has symbol
`(1 + 2 w_0 sum cos)^n ~ exp(-n w_0 k_perp^2)`, positive on the whole coarse zone and of fixed physical radius `sqrt(2 n w_0) a`
(`n w_0` chosen so the radius is a fixed fraction of the block size `L`).

**What it changes in the refit.** Only the block-variable step of `goodblock.py` and the choice of `(w_0, n)` (rerun the one-loop `wscan`
rule of cycle 3 for sigma^2(l), now over `n w_0`; rerun the photon, Z2 gates and the content check), then the same fit, halves and certificate
code. It removes the spatial checkerboard blindness, so the base action's closure should improve (the rectangle's closure6 = -0.67 is
plausibly the footprint of the blind mode: a blind mode is an unmodelled degree of freedom); that is a **hypothesis** to be tested, not a claim.

**What it changes in the certified column.** Nothing in the method: `cert_measured.py` takes the fitted couplings (b_F, b_A, b_T, b_R per plane
class) as input; the certified window in the (b_F, b_A) plane (0.19 in b_F at b_A = 0; c3c corners for larger b_A) and the budget for further
loops (section 3) are what the new fit is compared with. If the smoother variable has larger content it will also have larger b_F (less
noise): the certificate then says how far that can go (isotropic limit b_F about 0.19, spatial links, `18 b_F N_F* < 1`).

## 7. Unit tests

* **Photon (4D U(1) weak coupling).** The certified object is SU(2)-specific (Haar on S^3, Bessel laws of the fundamental channel); it
  gives nothing for U(1). The mechanism by which the column excludes the photon, the centre half, is the same one that makes it bind here:
  a centre-charged coupling above about 0.19 per plaquette (isotropic) fails the criterion; the photon's fundamental coupling is orders
  larger. Passed (no claim for U(1)).
* **Z2.** No Bessel law, no claim; the box is a strong-coupling (disordered) regime. Passed.
* **Finite subgroups.** The certificate uses continuous conditional densities on S^3 and the geodesic metric; no claim for atomic laws. Passed.
* **Deconfinement.** The measured point lies at L sqrt(sigma) = 2.80, above 1/T_c; the points below (b = 4, edge) have b_F ts 0.4 to 0.8 and
  are far outside the window (columns >= 2.8 by the linear value). Consistent. **Triviality, Banks-Zaks:** no existence claim. Passed.

## 8. Marks

| result | mark | substantive / definitional |
|---|---|---|
| the reduction of the column to `N_F, N_h, N_g` and the Bessel closed forms | **paper**, checked by quadrature | substantive (new nonlinear control of the fundamental channel) |
| certified `N_F*`, `zeta*`, columns 0.7318, 0.7611, 0.9640, 0.99988 | **certified** (`cert_measured.py`) | substantive (computer-assisted) |
| isotropic beta_F window 0.1924 etc. | **certified** (same code), not in Lean | computer-assisted |
| closure/budget statements | **numerical** (certified columns, uncertain truncation) | interpretation |
| `kMeas_column_lt_one`, `limitDprimeW_measured`, `measured_decay` | **Lean**, modulo `CertifiedMeasured` | arithmetic / composition |
| the measured fitted action satisfies D' (W1) | certified for the fitted truncated action only | much weaker than the mass gap |

Weaker / equal / stronger than the mass gap: **much weaker.** Every result is about one fitted effective action on the coarse torus
(plaquette family, with a rectangle extension in the paper statement).

## 9. Blueprint changes (proposed for `PROOF-BLUEPRINT.md`; not edited here)

* **P4.1'' (W1 halves, certified):** add "the measured blocked action at L sqrt(sigma) = 2.80 (beta = 2.3, b = 8, w = 2, base fit and the
  extensions ext_T, ext_R, ext_TR) is certified inside the W1 window (nonlinear column 0.73, 0.76, 0.96, 0.9999; central 0.71, 0.72, 0.94,
  0.95); Lean: `ProofPhase/Certified/Measured.lean` (`limitDprimeW_measured`, `measured_decay`, base + ext_T), named hypothesis `CertifiedMeasured`."
* **P4.1'' (isotropic window):** beta_F direction at beta_A = 0 certified to 0.1924 (c3c: 0.0685); beta_A direction unchanged (0.21 / 0.22,
  ceiling 0.275 / 0.29).
* **P3 (H1) / new open item:** truncation margin. The certified margin of the measured action over the budget of further centre-charged loops is
  0.036 (rectangle included); the loop expansion's convergence at this point is **open** (closure residuals).
* **The first "real click" row** (c3b table, "content PASS, H_TV EXCLUDED, H_W NOT_EXCLUDED") can now be read as "W1 window reached, certified for
  the fitted truncated action", with the open items H1LocalLip, truncation, ObsTransferPhys.

## 10. Next step

The decisive missing piece for this point is the **truncation margin**: refit the 2.80 point (GPU job, not rerun here) with the next loop
families (1x3, 2x2, bent) and re-certify with `cert_measured.py` (add the families' incidence counts; the code needs only their couplings and
counts). If their couplings stay below the 0.0013 budget the verdict survives; if not, the cleaner route is the non-blind smoother kernel
(section 6), which targets the source of the large closure residuals. In parallel (cheap, CPU): the class-resolved Lean column (counting lemma)
and the beta_A-direction tightening of the isotropic window (c3c section 9 items 1-2).
