# c9b-adjoint: the adjoint half gamma_A of the split one-box criterion (cycle 9, 2026-11-23)

Task: state precisely what `gamma_A` in `FineOneBoxSplit` (c8a, `Saturation/Reduction.lean`) must bound for the true conditional law at
the cell scale `L_1`; check whether the coupling-form Dobrushin-Shlosman theorem (M1) removes the worst-case-over-boundaries
requirement; find the cheapest honest route from what exists to a bound; check the noise-limit trap; formalise a generic comparison
statement if one falls out.

Lean: `formal/ProofPhase/Adjoint2/Transfer.lean` (new, 456 lines, imports only Mathlib), built in `~/formal-c9y` (`build.sh`,
"Build completed successfully"), 18 headline declarations checked by `axioms.sh` (`axioms.log`: each depends only on `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`, no new axiom). No existing `.lean` file was edited. Numerics: one
pre-registered CPU check (section 6, `n1_columns.py` / `.log`, under one minute). No GPU job.

**Round 2 correction (2026-11-23, `ROUND2.md` section 4):** the sup-form numbers below (`c0 + c1 = 2.40`, "sup form fails at 2.80") are the
crude two-point bound; the sharp sup-form column of the fitted action at 2.80 is 1.02 (uniform) and 0.96 (weighted).

Claim marks: **Lean** (built and axiom-checked here), **paper** (complete argument here), **sketch** (argument with constants or steps
not written out), **citation** (standard theorem, recalled, not re-proved), **numerical** (arithmetic or float computation here),
**open** (named, not proved).

---

## 0. Results in plain words

1. **What `gamma_A` is depends on the hybrid law, and c8a's prose has the labels the wrong way round** (section 1.1, paper). With
   c8a's stated hybrid (centre law as under the moved boundary `sigma'`, adjoint kernel as under `sigma`), the Lean `hA` slot
   (`q(sigma) <-> r`) measures the move of the **centre** law, not of the adjoint kernel. The Lean is unaffected (`r` is existential);
   the intended reading needs `r` = centre law under `sigma`, adjoint kernel under `sigma'`.
2. **The layer form of the split is ill-conditioned; the potential form is well-conditioned but does not separate the propagation**
   (section 1.2, paper). In the layer form the adjoint kernel at a fixed centre configuration sees the centre-charged (fundamental)
   couplings as adjoint couplings, through a discontinuous section or a hard Z2-monopole constraint; its sup-form column is at least the
   full column, **2.4 for the fitted action at the measured point** (N1, numerical). So the certified "adjoint half" numbers (0.0036,
   about 1e-3, c2a/c3c/c4d) do **not** bound the layer-form `gamma_A`, even for the fitted action. In the potential form (hybrid = old
   law tilted by the **centre-blind part of the boundary change**, Lean `split_tilt`, `delta0`), the adjoint **source** is the
   centre-blind change (fit: tiny), but its **propagation** is by the full box law, so `gamma_A` and `gamma_Z` share one factor
   `1/(1 - c)`, `c = c0 + c1` the full single-site column. **The split separates sources, not propagation.**
3. **The precise statement** (section 1.3, sketch): with a two-level coupling (coarse block variables first, then the fine content
   given the coarse data),

       gamma_A <= (|shell|/|Lambda_0|) [ b_UV + (1 + C_UV) beta0 / (1 - c0 - c1) ],

   where `b_UV`, `C_UV` are the ultraviolet (fine-given-coarse) terms, `beta0` the centre-blind boundary source, and `c0`, `c1` the
   centre-blind and centre-odd sup-form columns of the **true** coarse conditional specification at `L_1`, suprema over all coarse
   data and all UV-good fine outsides. The genuinely adjoint input is `c0` and `beta0`; the binding input is the common `c0 + c1 < 1`
   (named **H_adj(L_1)** and **H_prop(L_1)**, section 1.3). At `L sqrt(sigma) = 2.80` the fitted action has `c0 = 0.020` but
   `c0 + c1 = 2.40` (sup form): the sup-form propagation fails there for the fit itself, as c3b/c4d's "H_TV EXCLUDED" said; only the W1
   form (certified 0.73) passes, and W1 must then be converted to the one-box criterion's Hamming count by one smoothing step (sketch).
4. **Uniformity** (section 1.4). (i) Over centre configurations: only typical ones are needed (Lean, `abs_integral_bind_sub_le`: the
   difference of two mixtures over the same centre law is at most the per-configuration bound on a good set plus `2M` times the
   conditional probability of its complement). (ii) Over outsides: **the support-restricted coupling form removes the worst case over
   UV-bad fine outsides only** (as in M1, with composite boxes and Lemma C), not over the coarse data at `L_1`: the Wilson measure and
   its blocked law have full support and at `L_1` there is no small parameter making atypical coarse data rare. The worst case over the
   coarse data is benign in kind (compact, smooth, no frozen sectors in the centre-blind channel) but must be a bound on the **true**
   conditional density. Using the support restriction needs a pattern-conditioned assembly: `FineOneBox`/`FineOneBoxSplit` quantify over
   every boundary, so `couplingDS_bound` does not plug in as is (Lean gap, section 1.4).
5. **Routes** (section 2). (a) **Comparison, in mixed-variation form: recommended.** Proved here (Lean, `abs_tiltAvg_transfer`,
   `residual_budget`): the true influence is at most the fitted one plus a term controlled by the **residual's mixed variation** alone;
   the centre-blind residual column may be as large as `log 3 - 0.08 = 1.02` before the adjoint source becomes a problem. **Weakest
   link:** a worst-case (sup over coarse data) bound on the true conditional log-density's mixed variations at `L_1`. No fit supplies it
   (fits are averages, the closure residual was 67 %, c4d); no expansion reaches `L_1`. It is the fit-to-measure step, now stated as a
   local, testable quantity. (b) Bakry-Emery / log-Sobolev: fails for the fitted action at spatial links (row sum 3.2 against
   `Ric(S^3) = 2`, sketch) and does not touch true-versus-fit. (c) Computer-assisted finite box: not feasible rigorously (a continuum of
   fine variables per cell, uniformity in the lattice spacing).
6. **Noise-limit trap: excluded by construction in the one-box route, and the rule is stated** (section 3, paper). `FineOneBox` counts
   cells of full fine content, so no blocking enters the criterion; a blocking enters only an upper bound, and the two-level bound
   charges what a signal-losing block variable drops from the IR term to the UV term (`b_UV`, `C_UV`). The rule: `b_UV`, `C_UV` must be
   bounded by a mechanism that uses the block constraint's mass (M1's Lemma UV-TV); a decimation-like variable fails it instead of
   passing.
7. **Next step** (section 8): measure H_adj and H_prop together by constrained sampling of single-site conditional log-odds at `L_1`
   (both halves, worst-type backgrounds), with the same block variable for which the UV term is bounded; in Lean, the
   pattern-conditioned one-box assembly through `couplingDS_bound`.

---

## 1. What gamma_A must bound

### 1.1 The split and its hybrid (paper)

`FineOneBoxSplit` (Lean, c8a) asks, for every box `B`, outside cell `z`, boundary `sigma` and new value `s`, for a law `r` with

    |q(sigma) F - r F| <= kappa_A(z) L    (slot hA)       |r F - q(sigma') F| <= kappa_Z(z) L    (slot hZ),

`sigma' = sigma with z := s`, for gauge-admissible `F` of per-cell oscillation `<= L`. Then `kappa_A + kappa_Z` bounds the influence
(`isInfluenceBoundOn_split`) and `gamma_Z + gamma_A < 1` gives `FineOneBox` (`fineOneBox_of_split`). `r` is existential: the Lean
does not fix what "centre" and "adjoint" mean. Two readings:

* **Layer hybrid (L).** A measurable split of each cell's value into a centre part `zeta` and the rest; `q(sigma) = mu_sigma(dzeta)
  K_sigma(. | zeta)`. c8a section 5.1 takes `r = mu_{sigma'} (x) K_sigma`. Then `q(sigma) <-> r` differ by the **centre law** (same
  kernel) and `r <-> q(sigma')` by the **adjoint kernel**: the labels of c8a's prose are swapped relative to the Lean slots. The
  intended assignment is `r = mu_sigma (x) K_{sigma'}`: slot hA = adjoint kernel moved at the fixed centre law `mu_sigma`, slot hZ =
  centre law moved with the kernel `K_{sigma'}`. (A note for c8a's maintainers; nothing in Lean changes.)
* **Potential hybrid (P).** Write the box laws as tilts of one reference, `q(sigma) prop e^{H_sigma} nu`. Split the boundary change
  `H_{sigma'} - H_sigma = Delta0 + Delta1` into its **centre-blind** part (average over the centre partner of the new and old value,
  Lean `delta0`) and the **centre-odd** rest (`delta1`), and put `r prop e^{H_sigma + Delta0} nu`. Then slot hA is the response to the
  centre-blind part of the change, slot hZ to the centre-odd part (Lean `split_tilt`: each is bounded by the tilt lemma). Facts (Lean):
  a pure centre flip of `z` has no centre-blind part (`delta0_centre_flip`), the centre-blind part does not see the centre part of the
  new value (`delta0_centre_blind`), centre-odd weights have none (`delta0_eq_zero_of_odd`), centre-even weights have no centre-odd part
  (`delta1_eq_zero_of_even`).

### 1.2 Which hybrid: conditioning and propagation (paper)

**(L) is ill-conditioned.** A centre part of a cell must be a function of the SU(2) data. Two natural choices:
* a link sign relative to a measurable section `SO(3) -> SU(2)`: every such section is discontinuous (c2a section 2.1), and at fixed
  signs the fundamental term `beta_F/2 tr U_P` is a discontinuous function of the adjoint variables (a jump of `beta_F |tr|` across the
  cut);
* plaquette signs `eta_P = sign tr U_P` (gauge invariant): at fixed `eta` the adjoint configuration is confined to `{sign tr U_P = eta_P
  for all P}`, a hard constraint, and the fundamental term becomes `beta_F eta_P |tr U_P|/2`, an adjoint coupling of size `beta_F`.

Either way the adjoint kernel at fixed centre feels the centre-charged couplings. Quantitatively (c2a section 1.3, paper): the sup-form
adjoint column of the two-type split dominates the full sharp single-site column. For the base fit at `L sqrt(sigma) = 2.80`
(N1, numerical): full sup-form column 2.40 (spatial links), 0.99 (temporal). **So the layer-form `gamma_A` is not bounded by the
certified adjoint-half numbers, even for the fitted action;** those numbers bound the centre-blind potential `V0` of c2a's potential
split, a different object. c8a section 5.3's estimate "`gamma_A` of order `0.03/l`" conflates the two splits.

**(P) is well-conditioned, but propagation is shared.** In (P) both slots compare box laws of the **full** box specification; only the
boundary sources differ. By Dobrushin's comparison theorem (citation: Georgii, Gibbs Measures, Thm 8.20; Foellmer), for coarse
single-site coefficients `C_xy` of the box law with column `c < 1` and boundary sources `b_y(z)` (total-variation change of the
single-site conditional at `y` caused by the change at `z`),

    kappa^IR(z) <= sum_{x in B} sum_y D_xy b_y(z),   D = sum_n C^n,   sum_x D_xy <= 1/(1 - c).

The source splits, `b = b0 + b1` (tilt lemma and subadditivity of the oscillation), so `kappa^IR = kappa^IR_A + kappa^IR_Z` with the
common factor `1/(1 - c)`. A tie (two degenerate centre positions) contaminates (P)'s `kappa_A` too: any perturbation, centre-blind or
not, decides a tie. **No split of box influences isolates the adjoint half from the centre's propagation.** The clean isolation exists
one level down, for single-site coefficients: `C_xy <= (e^{Mix_xy} - 1)/2` with `Mix_xy <= Mix0_xy + Mix1_xy` (Lean
`abs_tiltAvg_transfer`, `residual_budget`), i.e. c2a's halves `c0 + c1`, now for the true conditional law.

**Recommendation: use (P), and state the adjoint input at the single-site level.**

### 1.3 The precise statement (sketch)

Objects. Cells = coarse links `b` at scale `L_1`; block variable `V_b in SU(2)` (the good blocking of c3b, `w = 2`); the fine content of a
cell. Box `Lambda_0` of side `l` cells; `|shell|` the number of outside positions with non-zero influence (about `8 l^3`, c7c section 1.3).

**Two-level coupling.** Couple the two box laws (`sigma`, `sigma'`) in two stages: first the coarse box variables (their laws
`rho_sigma`, `rho_{sigma'}`: the box law pushed through the blocking), then the fine content given equal coarse data. This gives

    kappa(z) <= (1 + C_UV) kappa^IR(z) + b_UV(z),

* `b_UV(z)`: expected number of box cells whose fine content differs although all coarse data agree (the direct fine boundary effect of
  `z`); `C_UV`: number of cells whose fine content a single coarse disagreement drags along. Both are fine-given-coarse quantities: M1's
  Lemma UV-TV (paper there, with citation-level inputs) bounds them on the scales where Balaban's machinery runs; the crossover from
  `L_0` to `L_1` is not covered (c3a's Lemma X).
* `kappa^IR(z)`: Hamming-Wasserstein distance of `rho_sigma`, `rho_{sigma'}` on the coarse box variables.

**Definitions** (all suprema over **all** coarse box data, all centre data, and the **UV-good** fine outsides; `H(V_x | rest)` is the
true conditional log-density of one coarse variable w.r.t. Haar, given the other coarse box variables and the fine outside):

    Mix_xy  = sup |H(v_x | w_y, .) - H(v_x | w'_y, .) - H(v'_x | w_y, .) + H(v'_x | w'_y, .)|        (mixed variation)
    Mix0_xy = the same for the part of H that is centre-even in the variable at y   (Lean delta0, pointwise in y)
    Mix1_xy = the same for the centre-odd part                                       (Lean delta1)
    c0 = sup_x sum_y (e^{Mix0_xy} - 1)/2,   c1 = sup_x sum_y (e^{Mix1_xy} - 1)/2      (sup-form columns; tanh(Mix/4) is the sharp form)
    beta0 = sup_z sum_y (e^{Mix0_yz} - 1)/2  (the centre-blind boundary source of one outside cell)

**gamma_A** (potential hybrid):

    gamma_A <= (|shell|/|Lambda_0|) [ b_UV + (1 + C_UV) beta0/(1 - c) ],   c <= c0 + c1 + (cross term, Lean exp_add_sub_one).

* **H_adj(L_1)** (named, open): `c0` small and `beta0` bounded at `L_1` for the true conditional law: "the centre-blind interaction of
  neighbouring cells is weak for every coarse configuration". The PREP reading "the adjoint layer is stateless" is this statement.
* **H_prop(L_1)** (named, open): `c0 + c1 < 1` in a form compatible with the Hamming count (sup form, or W1 plus one smoothing step:
  `TV(law(V_x | rest), law(V_x | rest')) <= Lambda sum_y d(V_y, V'_y)` with `Lambda` the sup of the Lipschitz constants of the true
  conditional density; then `kappa^IR_Ham <= n_adj + Lambda kappa^IR_W1`, sketch). `c1` is c8a's H_sat quantity in this language
  (plaquette approximation `18 tanh(Jbar) < 1`).
* Given both, `b_UV`, `C_UV` finite uniformly in the lattice spacing, and `l > (|shell|/l^3) [b_UV + (1 + C_UV) beta0/(1 - c)]/(1 - gamma_Z)`:
  `gamma_Z + gamma_A < 1` (sketch).

**Fit-side numbers** (N1, numerical, base fit box at `L sqrt(sigma) = 2.80`): `c0 = 0.020` (spatial), `0.013` (temporal); `c1 = 2.38`,
`0.98`. H_adj holds for the fitted action with a wide margin; H_prop fails for it in sup form at spatial links and holds in W1 form
(c4d, certified 0.73). So at this `L_1` the adjoint half is not what binds; the propagation (dominated by `F_ss = 0.17`) is.

### 1.4 Uniformity: over what, and what the coupling form buys

* **Centre configurations (layer reading; Lean `abs_integral_bind_sub_le`).** If `q = mu.bind K` and `r = mu.bind K'` with the same
  centre law `mu`, then `|q F - r F| <= eps + 2M mu(G^c)` with `eps` the per-configuration bound on a measurable good set `G`. So a
  bound uniform over **typical** centre configurations suffices. In box terms `M` is about `2 l^4` (per-cell oscillation 1 on `4 l^4`
  cells), so the atypical set must have conditional probability `<~ 0.01/l^3` per shell cell; for a saturated centre layer, tie-type
  configurations are suppressed like the area (c8a), which is ample (sketch).
* **Outsides: what the support restriction removes.** `couplingDS_bound` needs the influence hypothesis (I) only for pairs in the
  supports `Omega_0 x Omega_0'`. The SU(2) Wilson measure has a strictly positive density, so its support is everything; the gain
  appears only after conditioning on patterns (M1: `mu = sum_omega w_omega mu_omega`, bad regions as composite boxes, Lemma C:
  influence through the collar only, rarity of bad patterns). At the cell scale this removes the worst case over **UV-bad fine
  outsides** (large fields inside cells; rare at the fine scales by Balaban, within M1's range). It does **not** remove the worst case
  over the **coarse data at `L_1`**: the blocked law has full support there and there is no small parameter making atypical coarse data
  rare (the coarse variables are near Haar, c4d). Lemma C's collar idea applied at the coarse level would need such a rarity; without
  it, composite boxes are not rare and buy nothing.
* **Why the coarse worst case is acceptable in kind.** In M1 the worst case was fatal because of sub-block vortices with free positions
  (ties). In the centre-blind channel at `L_1` there are no discrete sectors (SO(3) data, connected and compact); the tie mechanism is in
  the centre-odd channel (`c1`, `gamma_Z`). The worst case over coarse SO(3) data of a bounded, smooth conditional density is controlled
  by its mixed variations. The difficulty is not the quantifier but the object: it must be the **true** conditional density.
* **Lean gap.** `FineOneBox` and `FineOneBoxSplit` use `IsInfluenceBoundOn` for **every** boundary condition. A support-restricted
  `gamma_A` therefore needs a new assembly: pattern-conditioned box laws, `couplingDS_bound` per pattern pair, the covariance form
  (UV-TV.md 33.3) and the average over patterns. The generic engine (`CouplingDS.lean`) exists; the assembly does not.

## 2. Routes to a bound

### (a) Comparison theorem, mixed-variation form (recommended)

**Provable now (Lean, done here).** True conditional log-density `H = Hfit + Psi`. The tilt lemma
(`abs_tiltAvg_add_sub_le`) bounds the change of a tilted average under a log-weight change of oscillation `delta` by `M (e^delta - 1)`;
the transfer (`abs_tiltAvg_transfer`) splits it as `M (e^{delta1} - 1) + M e^{delta1} (e^{delta2} - 1)`, fitted part plus residual
part; the column form (`column_lt_one_of_mix`, `residual_budget`) gives a Dobrushin column `< 1` once the fitted and residual mixed
columns sum to `< log 3 = 1.0986` (`log_three_gt`: `> 1.098`). This is the "TV-comparison lemma that transfers influence bounds between
two specifications with a controlled error", with the error measured in the residual's **mixed variation**, a local norm: the naive
whole-box total-variation comparison would cost `|B| x TV` per shell cell, i.e. a `gamma` error of order `l^3 TV`, useless.

**Sizes.** Centre-blind fitted mixed column `m0 = 0.082` (spatial), budget for the centre-blind residual `log 3 - m0 = 1.02` (N1). The
crude exponential form is a factor 2 weaker than the sharp `tanh(Mix/4)` per pair (N1(d): the sharp form is attained, the crude form
reaches 0.47 of its bound), so the real budget is larger. The centre-odd side has no budget at this `L_1` in sup form (`m1 = 9.5`).

**Needs new mathematics or computation.** A bound on `sup Mix0(Psi)` (sup over all coarse data, UV-good outsides) for the true blocked
conditional density at `L_1`. Fits do not give it: they are averages under the measure (Schwinger-Dyson / pseudo-likelihood), truncated,
with large closure residuals (c4d: 67 %). Options: (i) **measure it directly** (constrained sampling, section 8; numerical evidence, not
proof); (ii) a convergent expansion of the blocked conditional density at `L_1` (none exists; Balaban's stops while the coupling is
small); (iii) a reduction of the true `Mix0` to fine-scale quantities (open; I see no handle: the true mixed variation is a sup of a
log-ratio of fine integrals with constrained block data).

**Weakest link:** the worst-case bound on the true conditional density at `L_1`, i.e. H_adj and H_prop for the true law. It is
gap-strength in the sense of c2a section 4(a): any bound implying both halves implies the gap of the blocked theory.

### (b) Direct structural bound (Bakry-Emery / log-Sobolev)

**Provable now (citation).** On a product of unit 3-spheres (`Ric = 2`), a Gibbs measure whose potential has Hessian (row sum of the
block norms) `< 2` satisfies a uniform log-Sobolev inequality, for every boundary condition (the curvature bound is pointwise), hence
uniform exponential decay (Bakry-Emery; Stroock-Zegarlinski). Worst case over boundaries is free.

**Sizes (sketch).** A plaquette term `(beta/2) tr U_P` has second derivatives `<= beta` per pair of its links (unit-speed geodesics), so
the row sum is `4 beta x (plaquettes per link)`: base fit 3.2 (spatial), 1.3 (temporal) against 2 (N1). Fails at spatial links by a
factor 1.6. For the centre-blind part alone it passes trivially, but in the potential form the propagation needs the full potential.

**Needs.** The Hessian of the **true** conditional potential, sup over everything: the same true-versus-fit problem as (a), in a
stronger norm (second derivatives instead of mixed oscillations). Not recommended now; it becomes attractive if a smoothness bound of the
true density is ever available, since it is boundary-uniform by construction.

### (c) Computer-assisted finite box, worst case over small-field boundaries

The true conditional law of a box at `L_1` is an integral over `(l L_1/a)^4` fine links: no finite rigorous computation, and no
uniformity in `a`. A computer-assisted step is possible only on the **fitted** action (done: c3c, c4d) or on a reduced model; neither
is the true law. As a **measurement** it is c7b/c8b's one-box test (coupled heat-bath upper bound, telescoped lower bound), numerical
evidence only.

**Recommendation: (a)**, because its proved part already isolates exactly one local quantity (the residual's mixed variation) and its
budget on the adjoint side is wide; the remaining input is a measurable local statement (H_adj with H_prop) rather than a global one.

## 3. The noise-limit trap

**The trap** (blueprint P4.1''): a Dobrushin condition at `L_1` on block variables becomes cheap when the blocking loses the signal; the
difficulty moves into the observable transfer.

**Why it cannot make `gamma_A` small falsely here** (paper):
1. `FineOneBox` contains no blocking: sites are cells carrying their **full fine content**, influences count cells in Hamming distance,
   test functions are arbitrary gauge-invariant functions of the fine content. A small `gamma` is a statement about the Wilson measure.
2. A blocking enters only an **upper bound**, through the two-level coupling of section 1.3, and that bound is valid for every block
   variable. If the block variable is noise-like, `kappa^IR` and the fitted columns are small, but the fine content given noise-like
   coarse data still carries all the long-range physics: `b_UV`, `C_UV` are then of the size of the unblocked influence. The total
   cannot drop below the true `kappa` (it bounds it), so the trap moves the difficulty into `b_UV`, `C_UV`, where it is counted. This is
   c3a's difficulty conservation (`condDefect_eq`, Lean) in coupling form.
3. **Rule for any route that uses a block variable:** the UV terms must be bounded **with the same block variable**, by a mechanism that
   uses the block constraint's mass (Poincare in scale units, M1's Lemma UV-TV). Decimation has no such mass and fails the rule instead
   of passing. In addition, c3b's content check (fitted coarse adjoint and fundamental plaquettes resolved at `>= 3 sigma`) remains a
   necessary condition for reading a small fitted `c0` as physics; the measured point passed it (c4d, "content PASS").

**Where the trap still bites:** in routes that transfer a coarse D' condition through `ObsTransfer` (Route A); and in the reading of
the fitted adjoint numbers themselves: a small fitted `beta_A` is evidence for H_adj only together with content and a bounded UV term.

## 4. The owner's reading ("the adjoint layer is stateless")

In the terms above: "stateless" = `c0` small for the true conditional law (H_adj); "forgets at 1/e per tick" would be a contraction
`c0 <= 1/e` per step, far weaker than the fitted `c0 = 0.02`. The fit supports the reading. Two qualifications from this workstream:
(i) a stateless adjoint layer makes the adjoint **source** small, but a disturbance it injects travels through the full law, so the
smallness of `gamma_A` also needs the shared propagation `c0 + c1 < 1` (H_prop); (ii) "the adjoint layer at fixed centre" is not a
stateless object, because fixing the centre turns the fundamental coupling into an adjoint one (section 1.2). The reading is right for
the centre-blind **channel**, not for a **layer** obtained by conditioning on the centre.

## 5. Lean (`formal/ProofPhase/Adjoint2/Transfer.lean`)

Generic, no gauge content; standard axioms only (`axioms.log`).

* `tiltZ`, `tiltAvg` (`E_f[F] = ∫ F e^f dnu / ∫ e^f dnu`); `tiltZ_pos`, `tiltAvg_sub_const`.
* `abs_tiltAvg_add_sub_le`: `a <= g <= a + delta`, `|F - c| <= M`, `|f| <= B` ⇒ `|tiltAvg nu (f + g) F - tiltAvg nu f F| <= M (e^delta - 1)`.
* `exp_add_sub_one`, `abs_tiltAvg_transfer`: the change `g1 + g2` (oscillations `delta1`, `delta2`) ⇒ bound
  `M (e^{delta1} - 1) + M e^{delta1} (e^{delta2} - 1)`.
* `split_tilt`: the potential hybrid `r = tilt by f + d0` with `|q F - r F| <= M (e^{delta0} - 1)`, `|r F - q' F| <= M (e^{delta1} - 1)`.
* `sum_exp_sub_one_le` (`sum (e^{m_i} - 1) <= e^{sum m_i} - 1`), `column_lt_one_of_mix` (pair coefficients `<= (e^{m_z} - 1)/2`,
  `sum m <= S < log 3` ⇒ column `< 1`), `residual_budget` (`m <= mfit + mres`, `sum mfit + sum mres < log 3` ⇒ column `< 1`),
  `log_three_gt` (`1.098 < log 3`).
* `centreBar`, `delta0`, `delta1`; `delta0_add_delta1`, `delta0_centre_flip`, `delta0_centre_blind`, `delta0_eq_zero_of_odd`,
  `delta1_eq_zero_of_even`.
* `integral_bind_eq`, `abs_integral_bind_sub_le`: mixtures over the same law, good-set form.

Not formalised: the connection of `tiltAvg` to the measures of `BlockSpec` (via `withDensity`; mechanical), Dobrushin's comparison
theorem, the two-level coupling, the pattern-conditioned assembly.

## 6. CPU check N1

### 6.1 Pre-registration (written before the run; unchanged)

Script `n1_columns.py` (Windows Python, numpy only, CPU, expected runtime under one minute). Inputs: the base fit's box couplings from
`../c4d-certified/NOTE.md` (line 149): `|F_ts| <= 0.0545`, `|F_ss| <= 0.1725`, `|A_ts| <= 0.0011`, `|A_ss| <= 0.0020`, and the central
values `F_ts = 0.0540`, `F_ss = 0.1711`. Normalisation as in c2a section 1.4: sup-form per-incidence coefficients `tanh(beta_F)` (centre-odd)
and `tanh(2 beta_A/3)` (centre-blind), i.e. mixed second differences `D_F = 4 beta_F`, `D_A = 8 beta_A/3`; incidences: spatial link 6 ts + 12
ss, temporal link 18 ts.

Computed: (a) sup-form halves `c0` (centre-blind) and `c1` (centre-odd) per link type; (b) the centre-blind mixed column `m0 = sum D_A` and
the residual budget `log 3 - m0` of `residual_budget` (Lean); (c) the Bakry-Emery row sum `4 beta_F x (plaquettes per link)` against
`Ric(S^3) = 2` (sketch-level constant); (d) a randomised test of the tilt lemma `abs_tiltAvg_add_sub_le` on 20000 random discrete laws
(sizes 2 to 50, random `f`, `g` with oscillation up to 3, random `F`): the ratio of the observed difference to `M (e^delta - 1)`, and,
for comparison, to the sharp two-point form `osc(F) tanh(delta/4)`.

Predictions: (P1) `c0 < 0.05` for both link types; (P2) the full sup-form column `c0 + c1 > 1` for spatial links (consistent with c3b/c4d
"H_TV EXCLUDED" at `L sqrt(sigma) = 2.80`); (P3) `m0 < 0.15`, budget `> 0.9`; (P4) Bakry-Emery row sum `> 2` for spatial links;
(P5) no violation of the proved bound (max ratio `<= 1`); the sharp-form ratio also `<= 1`. Any failure of P5 means the Lean statement is
misread here (it is proved), and is reported as such.

### 6.2 Result (`n1_columns.log`; numerical)

| couplings | link | `c0` | `c1` | `c0 + c1` | `m0` | budget `log 3 - m0` | BE row (vs 2) |
|---|---|---|---|---|---|---|---|
| box | spatial | 0.0204 | 2.376 | 2.397 | 0.082 | 1.017 | 3.20 |
| box | temporal | 0.0132 | 0.980 | 0.993 | 0.053 | 1.046 | 1.31 |
| central F, box A | spatial | 0.0204 | 2.357 | 2.378 | 0.082 | 1.017 | 3.17 |
| central F, box A | temporal | 0.0132 | 0.971 | 0.984 | 0.053 | 1.046 | 1.30 |

P1-P4 PASS. (d): max ratio to `M (e^delta - 1)` is 0.469, no violation; max ratio to the sharp form is 1.0000 (attained, two-point
laws), no violation. P5 PASS. Reading: the crude bound proved in Lean is a factor about 2 weaker than the sharp one, never violated.

## 7. Unit tests (paper)

| model | `c0` (adjoint source/half) | `c1` / propagation | `gamma_A` (potential form) | verdict, correct? |
|---|---|---|---|---|
| compact U(1), Coulomb | 0: Wilson `cos` is odd under `theta -> theta + pi` (`delta0_eq_zero_of_odd`) | fails (c2a: `c_TV ~ 17.5`) | `beta0 = 0`, but `c >= 1`: no bound | fails through the propagation; gapless: correct |
| SU(2) x U(1), twist `(-1, 1)` | U(1) part is centre-even: in `c0`, Coulomb-size | SU(2) part small | `>= 1` (harmonic measure, c7c) | fails through `gamma_A`: correct |
| mixture of two confined phases | centre-blind data differ between phases | — | `>= theta` by telescoping (c7c) | fails: correct |
| Z2, either phase | 0 (all Z2 factors odd) | `c1`: passes confined, fails deconfined | 0 | decided by the centre half: correct |
| 2I, weak coupling | frozen centre-blind sectors (A5 orders) | ties | large | fails: correct |
| SU(2), strong coupling | `~ 18 tanh(2 beta_A/3)`, small | small | `O(1/l)` | passes (c7c/c8c anchor): correct |
| SU(2), `beta = 2.3`, `L sqrt(sigma) = 2.80` | fit 0.02 (true: H_adj open) | fit 2.4 sup / 0.73 W1 (true: open) | open | the claim |

The layer form would wrongly assign the U(1) Wilson coupling's propagation to the adjoint kernel at fixed centre (it becomes an
adjoint coupling there); the potential form puts it where c2a's photon test needs it (centre half).

## 8. Next step

1. **Measurement (GPU, a pre-registration of its own; not run).** Constrained sampling at `L_1`: fix all coarse variables except
   `V_x` and one neighbour `V_y` (sampled backgrounds plus extremes: block-flat, random Haar, twisted, large coarse curvature), sample
   the fine fields of the cells around `x`, estimate the conditional log-density of `V_x` on a grid of `v_x` and its mixed second
   difference under moves of `V_y`; split by `delta0`/`delta1` (average over `+-V_y`). Output: `Mix0_xy`, `Mix1_xy`, hence `c0`, `c1` for
   the true law, against the fit's 0.02 / 2.4. Same run as H_sat's (c8a section 6.3) with the adjoint column added; same block
   variable as the UV bound; controls: U(1) (`c0 = 0` exactly, `c1` large), 2I (sectors). A pass needs `c0` small (H_adj) and
   `c0 + c1 < 1` in sup form or W1 (H_prop); at 2.80 the fit predicts H_adj pass, sup-form H_prop fail: the decisive point is a larger
   `L_1` (`F_ss` falls) or the W1 form.
2. **Lean, reachable:** (a) `tiltAvg` as the integral against `BlockSpec` kernels (`withDensity`), so `split_tilt` discharges the two
   slots of `FineOneBoxSplit` for box laws with a density; (b) Dobrushin's comparison theorem in the coupling form of `CouplingDS.lean`
   (single-site sources, column `< 1`), giving `kappa^IR <= beta/(1 - c)`; (c) the pattern-conditioned one-box assembly
   (`FineOneBoxOn`: influences on supports only, `couplingDS_bound` per pattern pair, average over patterns).
3. **Fix in c8a's prose** (section 1.1): the hybrid should be "centre law as under `sigma`, adjoint kernel as under `sigma'`", or the
   potential hybrid of this note; and c8a section 5.3's `0.03/l` estimate should be withdrawn (layer/potential conflation).

## 9. Files and commands

* Lean: `formal/ProofPhase/Adjoint2/Transfer.lean`.
* Build (one-time `mkdir -p ~/formal-c9y && cp -a ~/formal/.lake ~/formal-c9y/`):
  `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/build.sh`;
  axioms: `axioms.sh` -> `axioms.log`. The build folder `~/formal-c9y` was deleted at the end of this workstream; recreate it to rebuild.
* Numerics: `py n1_columns.py > n1_columns.log` (Windows Python with numpy).

## 10. Not checked

Dobrushin's comparison theorem, Bakry-Emery and Stroock-Zegarlinski are recalled, not re-read. The Bakry-Emery row sum uses a rough
Hessian constant (per pair of plaquette links `<= beta`) and is a sketch. The two-level coupling bound and the W1-to-Hamming smoothing
step are sketches (no constants derived). M1's Lemma UV-TV is used as stated in `m1-tools/UV-TV.md` section 32 (paper there, with
citation-level inputs) and does not cover the crossover to `L_1`. The fitted couplings are taken from c4d as stated there; nothing was
refitted.
