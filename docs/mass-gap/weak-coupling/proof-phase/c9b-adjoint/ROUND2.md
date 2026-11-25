# c9b round 2: the infrared side of the one-box route (cycle 9, 2026-11-23)

Task (from the coordinator): (1) does the W1 form, with one smoothing step, give the one-box cell count the assembly needs (Lean if
reachable: Dobrushin's comparison theorem in coupling form on `CouplingDS.lean`), and does a larger `L1` improve the sup-form column (existing
fits only, pre-registered CPU check); (2) the pattern-conditioned one-box assembly (influence bounds only for in-support pairs, M1's
composite-box idea): state it, prove what is reachable; (3) draft, not run, the GPU pre-registration for the true law's `c0`, `c1` at `L1`.

Lean: `formal/ProofPhase/Adjoint2/CostCoupling.lean` (new, 602 lines) and `formal/ProofPhase/Adjoint2/PatternAssembly.lean` (new,
290 lines), built in `~/formal-ir` (`build-ir.sh`, "Build completed successfully", no warnings in the new files), 20 headline
declarations checked by `axioms-ir.sh` (`axioms-ir.log`: each depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no
`native_decide`, no new axiom). No existing `.lean` file was edited. Numerics: one CPU check N2 (pre-registered in `PREREG-N2.md`, but voided as a
pre-registered result by its own control rule, section 0; `n2_sharp.py`/`.log`, 43 s) and one post-hoc diagnostic (`n2_posthoc.py`/`.log`, marked as such). No GPU job. `PREREG-GPU.md`: draft only.

Claim marks as in `NOTE.md`: **Lean**, **paper**, **sketch**, **citation**, **numerical**, **open**.

---

## 0. Results in plain words

**Status of N2 (read first).** N2 was pre-registered (`PREREG-N2.md`), but control P7(iii) failed and the pre-registration says a P7
failure voids the run as a pre-registered result. The cause is the reference value: the pre-registration compared the central fit's
crude column (2.370) with round 1's box-corner value (2.397); the post-hoc check reproduces 2.3968 at the box corner, and controls (i),
(ii) agree to 5e-5. So **every N2 number below is a numerical diagnostic, not a pre-registered result.** The pre-registered tolerance
("1e-3 (relative 1 %)") is also ambiguous; the code used 1e-2 relative for (i), (ii) and 0.02 absolute for (iii) (dated amendment in
`PREREG-N2.md`).

1. **Round 1's "column 2.4 at 2.80" is the crude two-point bound; the sharp sup-form column of the fitted action is 1.02** (N2,
   numerical; the coefficients are quadrature maxima from a 4-parameter search, not certified suprema). The sharp pair coefficient is
   0.424 `beta_F` at small coupling (4/(3 pi); quadrature agrees to 5e-5), 0.42 to 0.45 of `tanh(beta_F)` at every fit with
   `L sqrt(sigma) >= 2.06`, larger at strong coupling. At 2.80 the uniform sharp column is **1.021** (central; 1.036 at the c4d box
   corner): **still above 1, by 2 %**. Only the **weighted** form (spectral radius of the link-type matrix, post-hoc) is below 1:
   **0.960** (0.975 at the box corner). So round 1 overstated the size of the failure; for the uniform form it did not misstate its sign.
2. **W1 plus one smoothing step gives a count that is finite and uniform in the box size, but very sensitive to the W1 margin**
   (Lean: the generic comparison theorem and the smoothing step; paper: the colour-class composition; numerical: the constants).
   Plaquette fit at 2.80 (W1 column 0.7318, c4d): TV-Lipschitz column 0.511 per radian, colour-class amplification `K_s = 2.25`,
   `kappa_Ham <= 12.2` per outside link, box side `l >= 99` cells (`gamma_Z = 0`; 197 for `gamma_Z = 1/2`). **With c4d's rectangle fit
   (ext_R, W1 column 0.964, a real coupling) the same count gives `kappa_Ham` about 99 and `l` about 800, before the rectangle's own TV
   contributions are added; at ext_TR's knife edge (0.9999) it is 2.4 x 10^5.** The weighted sup-form route at 2.80 gives
   `kappa_Ham <= 71`, `l >= 568` (post-hoc). **For the true law all of this is open**: it needs the true conditional law's W1 column well
   below 1 and a finite Lipschitz constant (measured by `PREREG-GPU.md`).
3. **A larger `L1` improves the sup-form column strongly, for the fits that exist; none of them has content** (N2). Sharp sup-form
   column: 1.02 (2.80, content PASS), 0.89 (2.92), 0.62 (4.13), 0.55 (5.60); direct Hamming route there `kappa_Ham <= 7.9, 1.6, 1.2`,
   `l >= 65, 15, 12`. But 2.92, 4.13 and 5.60 failed c3b's content check (coarse 3^4 lattice, Creutz ratio not resolved): exactly where
   the noise-limit trap makes columns look small. **No conclusion for the true law at larger `L1` until a fit with content exists there.**
4. **The pattern-conditioned assembly is stated and proved down to one named input** (Lean). `FineOneBoxPat T` ⇒ `FineDecayInv` ⇒ full
   assembly (`fineDecayInv_of_fineOneBoxPat`, `yang_mills_assembly_pat`). Its content sits in `DisintBound` on the good patterns: the
   Wilson measure conditioned on the content near the near observable, with a bound on the conditional averages of the far observable
   **for content pairs in a set of full measure only**. A separate lemma (`pair_bound_of_couplingDS`) gives such a pair bound from M1's
   coupling theorem with influence hypotheses on the supports only; **wiring it into `DisintBound` (the content set versus the coupling
   supports, constants uniform over the content pairs) is not done.** As stated, the pattern clauses do not force a non-trivial pattern
   set (one pattern satisfies them; reviewer finding): the rarity and index-decorrelation inputs (M1's H2, H1) enter only when a pattern
   decomposition is used to supply `DisintBound`.
5. **The GPU measurement is drafted** (`PREREG-GPU.md`): constrained sampling of single-link conditional laws at `L1`, measuring the sharp
   coefficient, its centre-odd and centre-blind halves, the W1 coefficient, the smoothing constant and c8a's `Jbar` (H_sat at block level
   1) in one run; U(1) and 2I gates; staged plan; nothing runs without the owner's OK. Expected at 2.80: the sup form UNDECIDED (the fit
   predicts 0.96); the decisive quantities there are H_adj and the W1 column including rectangles.
6. **P1 also failed** (ratio sharp/crude in `[0.35, 0.55]`): at `L sqrt(sigma) = 0.73` and `1.03` (ratios up to 0.70, and 1.30 where the
   adjoint tilt factor `q(D)` is large; there the quoted value is the quadrature maximum times `q(D)`, which exceeds the crude bound).

---

## 1. W1, one smoothing step, and the cell count (item 1)

### 1.1 The argument (paper; constants sketch-level)

Box `Lambda_0` of `l^4` coarse sites (`4 l^4` links), two boundary conditions differing at one outside link `z0`. Single-link conditional
specifications of the two box laws coincide except at the links sharing a plaquette with `z0`.

1. **W1 comparison** (Lean for a generic bounded cost, `costDS_bound`; the SU(2) geodesic cost `d <= pi`, the single-link blocks and
   the source terms next to `z0` are the paper instantiation).
   With W1 pair coefficients `K_xy` (c4d) and column `c_W = max_y sum_x K_xy < 1`, there is a coupling of the two box laws with
   `sum_x E d(V_x, V'_x) <= D := pi c_W/(1 - c_W)` (the source of an arbitrary change at `z0` is at most `pi` times its W1 column).
2. **One smoothing step** (Lean, `cost_bind_le`; the colour classes are paper). Colour the links by (direction, parity of the transverse
   coordinate sum): 8 classes, no two links of a class share a plaquette (checked by enumeration, N2). A heat-bath pass over one class is
   an exact stationary update of both box laws, and couples the two copies link by link maximally. Doing the 8 passes in a fixed order:
   a link of class `k` disagrees after its pass with probability at most
   `src_x + sum_{y earlier} C_xy 1[y disagrees] + sum_{y later} Lam_xy d(V_y, V'_y)` (`C` sharp sup-form, `Lam` TV per radian). Hence
   `kappa_Ham(z0) <= K_s (col_TV + Lam_col D)`, `K_s` the maximal column sum of `sum_{n < 8} Lhat^n` (`Lhat` the class matrix of earlier-to-
   later coefficients, best order chosen).
3. **Test functions** (Lean, `abs_integral_sub_le_osc`, `abs_integral_sub_le_costSmooth`, `isInfluenceBoundOn_of_costSmooth`): a function
   of the box with per-site oscillation `<= L` moves by at most `L kappa_Ham`: the influence slot of the one-box criterion.
4. **Cell count**: `OneBoxSum` sums over outside **site positions** `u` (each `kappa(u)` bounds every link at `u`, and every link is
   covered `|Lambda_0| = l^4` times; `gdsw_of_oneBox`); `N_adj(l) = 8 l^3 + 12 l^2` positions carry a link sharing a plaquette with the box
   (enumerated, N2); the one-box sum is below `1 - gamma_Z` once `(8/l + 12/l^2) kappa_Ham < 1 - gamma_Z` (rate `lambda -> 0`; any fixed
   `lambda > 0` costs a factor `e^{lambda E}`). (Counted per outside link instead, `28 l^3 + 12 l^2` links against box volume `4 l^4`:
   `l_min` about 86 at `kappa = 12.2`; the site form is the one `FineOneBox` uses.)

**Scope.** This is the **coarse-level** one-box criterion for the blocked specification (sites = coarse links with their SU(2) value). The
step to `FineOneBox` (sites = cells with their full fine content) is the two-level coupling of `NOTE.md` section 1.3, still a sketch: the
UV terms `b_UV`, `C_UV` multiply the coarse count.

**Tilt factor** (paper; used in N2 for the adjoint terms of the other plaquettes). If `rho_i' = rho_i w/E_i w` with `w in [1, e^D]`, then
`2 TV(rho_1', rho_2') <= int w |rho_1 - rho_2|/E_1 w + |E_2 w - E_1 w|/E_1 w <= e^D 2 TV + (e^D - 1) TV` (the second term: `w - c` with
`c` the midpoint of the range of `w` has `|w - c| <= (e^D - 1)/2`), so `TV' <= q(D) TV`, `q(D) = (3 e^D - 1)/2`. The same factor holds for
the TV-Lipschitz constant (limit of `TV/delta`).

### 1.2 Numbers for the fitted action (N2 and post-hoc; numerical diagnostics)

| `L sqrt(sigma)` | content | crude column (N1 form) | sharp sup column | weighted (spectral radius, post-hoc) | TV-Lipschitz column (/rad) | count `kappa_Ham`, `l_min` |
|---|---|---|---|---|---|---|
| 2.80 (central) | PASS | 2.370 | 1.021 | 0.960 | 0.511 | W1 + smoothing, plaquette fit (c_W 0.73): 12.2, 99; with ext_R (c_W 0.964): 99, 796; weighted sup: 71, 568 |
| 2.80 (box corner) | PASS | 2.397 | 1.036 | 0.975 | 0.519 | W1 + smoothing (c_W 0.73): 12.5, 102; weighted sup: 112, 902 |
| 2.92 (beta 2.5, b=16) | NO_CONTENT | 2.071 | 0.888 | 0.835 | 0.444 | direct Hamming: 7.9, 65 (weighted 14.6, 119) |
| 4.13 (beta 2.4, b=16) | NO_CONTENT | 1.456 | 0.621 | 0.583 | 0.311 | direct: 1.64, 15 |
| 5.60 (beta 2.3, b=16) | NO_CONTENT | 1.296 | 0.552 | 0.518 | 0.276 | direct: 1.23, 12 |
| 2.06, 1.46, 1.40, 1.03, 0.73 | NO_CONTENT | 4.6 to 16.9 | 2.06 to 17.7 | 1.94 to 17.2 | 1.0 to 10.3 | none |

Pair coefficients at 2.80 (central): `C(s<-ss) = 0.0735`, `C(s<-ts) = 0.0232`, `C(t<-ts) = 0.0231`; `Lam = 0.0368, 0.0116, 0.0116` per
radian. The maximum found is always the antipodal flip with zero rest field (`A_r = 0`, `psi = pi`); the search covered `psi` in
`[pi/2, pi]` only (a reviewer's sweep over `[0, pi]` at the central ss coupling found TV increasing up to `pi`). `K_s = 2.254` (best class
order (0, 1, 2, 7, 5, 6, 4, 3)). The direct Hamming route uses the uniform column; the weighted one uses the column-form type matrix
(post-hoc; a first version used the row-form matrix: same spectral radius, wrong weights, count 212 instead of 71; corrected after review).

**Reading.** (i) At 2.80 the fitted plaquette action is just outside the uniform sup-form window (1.02), just inside the weighted one
(0.96), and inside the W1 window (0.73; **0.964 once the fitted rectangle is included**, c4d). (ii) The W1-plus-smoothing count is finite
but scales like `1/(1 - c_W)`: about 100 cells at 0.73, about 800 at 0.964, and it is not robust to further loop families (c4d's
knife-edge ext_TR). The rectangle's own sup-form and Lipschitz contributions are not in N2. (iii) The decisive numbers are the **true
law's** coefficients including the rectangle and longer loops. (iv) Larger `L1` would help a lot if the fits there could be trusted;
they cannot yet (no content).

### 1.3 What the Lean proves (`CostCoupling.lean`)

* `SiteCost`, `cst`, `ecost`, `costPhi`; `hamming` and `ecost_hamming` (`E[1[Y_x != Y'_x]] = pi(Y_x != Y'_x)`).
* `ecost_bind_of_notMem` (sites outside the block keep their expected cost), `block_cost_le` ((I) in cost form, integrated),
  `cost_bind_le` (**one smoothing step**, any input/output cost families, linear propagation at in-support pairs).
* `costPhi_T_le` (one step of the averaged update: `Phi(T pi) <= theta Phi(pi) + sum_b a_b/N`), `CostWeights` (weights, **source terms
  `a_b`**, influence numbers, column condition), `CostWeights.costPhi_iter_le`, **`costDS_bound`** (Dobrushin's comparison theorem in
  coupling form, any bounded cost: a coupling with `sum_x v_x E d_x <= sum_b a_b/((1 - gamma) c_min) + eps`). With the Hamming cost and
  `a_b = 0` on good blocks it is M1's `couplingDS_bound`.
* `abs_sub_le_card_disagree` (telescoping), `abs_integral_sub_le_osc` (coupling bound for per-site-oscillation test functions).
* `CostSmoothData`, **`abs_integral_sub_le_costSmooth`** (W1 comparison + one smoothing step: `|int F dmu - int F dmu'| <= L (a_0 +
  Lambda_bar sum_b a_b/((1 - gamma) c_min))`), **`isInfluenceBoundOn_of_costSmooth`** (the influence slot of `FineOneBox` /
  `IsInfluenceBoundOn` from such data for every boundary pair).

Also `influence_source_block` (added after review): every block satisfies (I) with `K = 0` and `a_b = Σ_{y ∈ B_b} v_y D_y`, so M1's
`couplingDS_bound` (Hamming cost, source blocks with `a_b = Σ v_y`, good blocks with `a_b = 0`) is the special case of `costDS_bound`.

Not formalised: the colour-class composition (the smoothing kernel `Sm.Q b'` is one kernel; composing 8 passes into it and its bound is
paper; the matrix arithmetic of `K_s` is N2), the instantiation with the blocked specification, the SU(2) geodesic cost and the W1/TV
coefficients, the two-level (coarse-then-fine) coupling.

## 2. The pattern-conditioned assembly (item 2)

### 2.1 Why a new assembly (paper)

`FineOneBox` feeds `theoremA_on`, which contracts **oscillations**: `OscBound h v` is a statement about every configuration, so the influence
bound is used at every boundary condition. M1's coupling form (`couplingDS_bound`) needs (I) only at pairs in the supports. To use that,
the covariance must be produced by couplings rather than by oscillation contraction, which is `UV-TV.md` 33.3's covariance form: condition
on the content `y` near the near observable `F`; `Cov(F, G) = E[phi(y) (E[G | y] - E G)]`, and `E[G | y] - E G` is an average over a second,
independent content `y'` of `E[G | y] - E[G | y']`: two **sampled** contents, both in the support.

### 2.2 Statement and proof (Lean, `PatternAssembly.lean`)

* `covar`, `abs_covar_le_two`, **`cov_mixture`** (`Cov_mu = sum_p w_p Cov_{nu_p} + index covariance`), **`abs_covar_mixture_le`** (good
  patterns `<= eps`, bad patterns `<= 2` each, plus the index term).
* `DisintBound nu F G eps`: `nu = eta.bind K` over a content type `Y`, `F = phi(y)` a.s. under `K y` (`|phi| <= 1`), a measurable `Omega` of
  full `eta`-measure, and `|int G dK_y - int G dK_y'| <= eps` **for `y, y'` in `Omega` only**. **`abs_covar_le_of_disintBound`**:
  `|Cov_nu(F, G)| <= eps` (`|G| <= 1`).
* **`pair_bound_of_couplingDS`**: the pair bound from M1's theorem for two conditional measures whose `CouplingSpec` asks (I) on their
  supports only: `|int g dK_y - int g dK_y'| <= 2 v_min^-1 s/((1 - gamma) c_min)`. Not wired into `DisintBound`: that needs, for every pair
  of contents in `Omega`, a `CouplingSpec` with uniform constants, and the relation of `Omega` to the coupling supports (open).
* Reviewer note: the pattern clauses of `FineOneBoxPat` are satisfiable by a single pattern (weight 1, index term 0), so all the content
  is in `DisintBound`; patterns help in **supplying** `DisintBound` (per pattern, composite boxes), not in the statement.
* **`FineOneBoxPat T`** (named, open): rate `m > 0`; for every extent `R` a constant `c` and a level `k0`; for `k >= k0` and every volume the
  Wilson measure is a finite mixture over patterns (tested on bounded measurable functions); for every pair `F`, `G` as in `FineDecayInv`
  at physical distance `D`: good patterns with bad weight `<= c e^{-mD}`, index covariance `<= c e^{-mD}`, and a `DisintBound` with
  `eps = c e^{-mD}` on every good pattern.
* **`fineDecayInv_of_fineOneBoxPat`** (constant `4c`) and **`yang_mills_assembly_pat`**: `OnLCP' ∧ NonTrivial ∧ FineOneBoxPat ⇒
  TorusDecayLoc ∧ MassGapLoc ∧ MassGapMFLoc ∧ LimitRP ∧ NonTrivial`.

### 2.3 How M1's composite boxes enter, and what is open (sketch / open)

For a good pattern `p` and two sampled contents `y, y'` near `F`: the conditional measures `K_y`, `K_y'` on the complement are coupled by
`couplingDS_bound` with the block family of `UV-TV.md` 16: good boxes (translates of `Lambda_0` away from bad cells; (I) from the one-box
influence, now needed only in the supports), composite boxes `W(K)` around bad clusters (Lemma C: influence through the collar only),
source blocks next to the conditioned region. Weights `v_x = e^{-lambda dist(x, supp G)}` turn the column condition into the one-box sum (as
in `M1/UVTVScale.lean`, `ScaleHyp.weights`). Open, each named: (a) **coverage** with composite boxes (repeating each composite box until its
coverage dominates its boundary influence; "needs checking in detail", `UV-TV.md` 16); (b) **Lemma C at the cell scale** (its proof uses
small-field data on both sides of the collar: available on the scales where Balaban's machinery runs, **not** through the crossover to
`L1`, the same limit as c9b's section 1.4); (c) **rarity** of bad patterns at the cell scale (M1's H2); (d) the **index decorrelation**
(M1's H1). The support restriction removes the worst case over **UV-bad fine outsides** only; the coarse worst case at `L1` stays (round 1,
section 1.4), and is what `PREREG-GPU.md` measures.

## 3. The GPU draft (item 3)

`PREREG-GPU.md`. One run measures, per pair class and background: the sharp sup-form coefficient (centre flip and centre-blind rotation),
its centre-odd and centre-blind halves (`c1`, `c0`), the W1 coefficient, the smoothing constant, and c8a's `Jbar` (H_sat at block level 1).
Primary point 2.80; secondary 4.2 with a content check first. Gates: U(1) `beta = 1.1` (fail expected), 2I `beta = 6` (frozen pairs
expected), CPU pilot at `beta = 0.5`. Verdict bands fixed (H_adj, H_prop sup form, H_prop W1 + smoothing, H_sat, tail rule, noise-limit
rule). Timing: CPU pilot, then one 30-minute GPU job (owner's OK), then the projection `t_eff x N_eff x 720` ensembles for the primary,
staged A-D, each stage with its own OK; precision relaxed if Stage A exceeds 24 GPU-hours.

## 4. Corrections to round 1 (`NOTE.md`)

* Section 0 item 3 and section 1.3 "Fit-side numbers": `c0 + c1 = 2.40` is the **crude** sup form; the sharp uniform sup-form column of
  the fit is 1.02 (spatial, central), still above 1; the weighted form is 0.96 (post-hoc). "The sup-form propagation fails there for the
  fit itself" holds for the crude and the uniform sharp form (by 2 %), not for the weighted form.
* Unit-test row "SU(2), beta = 2.3, 2.80": "fit 2.4 sup" should read "fit 2.4 crude / 1.02 sharp / 0.96 weighted sup".
* The W1 number 0.73 used there is the plaquette fit; with c4d's fitted rectangle it is 0.964.

## 5. Not checked

The colour-class amplification `K_s` is computed on the class-level matrix of column sums (an upper bound for nonnegative matrices,
paper); the smoothing count and `l_min` are sketch-level constants for the fitted action, not certified. The sharp coefficients are
quadrature maxima found by a 4-parameter search (coarse grid plus 80 random local steps; `psi` restricted to `[pi/2, pi]`), not certified
suprema; the maximum found sits on the boundary (`A_r = 0`, antipodal flip) for every fit, which is where small-coupling analysis puts it. The rectangle class is not in N2 (only c4d's
W1 number). Dobrushin's comparison theorem is now Lean (generic); the box-level instantiation is not. `PREREG-GPU.md`'s sample-size
estimate uses the near-uniform Fisher information and has not been piloted.

## 6. Review

Two read-only reviewers (one on the Lean statements against this note, one on the numerics and pre-registrations). Applied: the
M1-reduction wording and `influence_source_block`; the `DisintBound` wiring and single-pattern remarks; generic-cost wording; the
smoothing-kernel docstring; N2 voided as a pre-registered result; the post-hoc type matrix corrected (column form); the rectangle
sensitivity of the count; the P1 failing points; claim wording in sections 0 and 4; GPU draft counts, tail rule, max over listed moves,
power, pilot, W1 fail band, penalty bias. Not applied: re-counting the one-box sum per outside link as the main number (the site form is
`FineOneBox`'s; both are given in 1.1).

## 7. Files and commands

* Lean: `formal/ProofPhase/Adjoint2/CostCoupling.lean`, `formal/ProofPhase/Adjoint2/PatternAssembly.lean`.
* Build (creates `~/formal-ir` from `~/formal/.lake` if missing):
  `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/build-ir.sh ProofPhase.Adjoint2.PatternAssembly`;
  axioms: `axioms-ir.sh` -> `axioms-ir.log`. `~/formal-ir` is deleted at the end of the round.
* Numerics: `py n2_sharp.py > n2_sharp.log` (pre-registered, `PREREG-N2.md`); `py n2_posthoc.py > n2_posthoc.log` (post-hoc; imports
  `n2_sharp_lib.py`, the function part of `n2_sharp.py`).
* Drafts: `PREREG-GPU.md`. Handover: `HANDOVER.md`.
