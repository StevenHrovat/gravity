# M1 referee review 3 (adversarial), 2026-11-22

Scope: the pieces new since REVIEW-2: `../m1-tools/REVIEW2-RESPONSE.md` (all of it), `DECODER-LOCAL.md` (update note
and the parts the response keeps), `WRITEOUTS.md` 1-2, `S1-CURRENT.md`, `FILL.md` (with its G6 update), `HANDOVER.md`
updates, `M1-PLAN.md` 0 (status and final verdict). Read for reference: `CLOSING.md`, `CLOSE-OUT.md` 2 and 4,
`SKETCH-STEPS.md` 1, `S1-PROOF.md` 5, `EXTERNAL.md`, REVIEW-2; the Lean files `Exact.lean` (in full) and
`Assembly.lean` (row structure only). Balaban, text layer extracted with `pdftotext` from the local PDFs: [V]
pp. 377-392 ((1.70)-(1.104)) and [III] pp. 259-260 ((2.25)-(2.33)). Nothing was built or re-run.

## Verdict

M1's claim of a complete paper-level argument does not stand yet. I found no FATAL error: the decoder's new Peierls
bound is correct and volume-uniform, the count `16 b = 1.49 > 1` is right, the slab gap is area-independent, and the
extension of the conditional step to complex weights by linearity is sound (it divides only by the reference fibre
integral). But three load-bearing steps are asserted rather than argued: (1) that a labelled polymer can be written as
a constant times `exp` of a *small* local term (Balaban's bounds are one-sided, and without this the labels fall back
into the large-field bookkeeping whose cost diverged in REVIEW-2); (2) how the decoder's conflict components, whose
extent is decided non-locally, enter Balaban's polymer representation; (3) the large-field split in R10, which treats
a property of the history as an event of the top block field and converts density bounds to probabilities with a
bare-scale normalisation that does not reach scale `K`. And the one-step induction `S1-CURRENT.md` is a table of
deltas without the order of constants. I would rate M1 as "complete programme, counting and decoder probability fixed,
four lemmas to write", not as a paper-level argument modulo [I] Theorem 2 and P4.

## Findings, most severe first

### H1. Labels: the factor `a_l (1 + h_l)` with `h_l` small is asserted, not derived

* **Location.** `REVIEW2-RESPONSE.md` 2 ("`h_l` is analytic, local, gauge-invariant and small"); `WRITEOUTS.md` 1
  step 2 ("Write `F_l(Y_a) exp(-Sum R_0) = a_l (1 + h_l(V))` with `h` analytic, local and small"), step 3 ("one of the
  R-terms of [III] (2.30)"); `S1-CURRENT.md` (F-f).
* **Claim.** After release, each labelled polymer is a constant `a_l` times `exp(log(1 + h_l))`, an R-term with a
  discrete index, with no per-step cost.
* **Failure.** Everything Balaban proves about a polymer activity is an **upper** bound: [V] (1.73)-(1.75) bound
  `|T_k(X,(U,J)) F|` by `e^{3 sup|Delta|} sup|F| T_k(X,(U,0)) 1`, and (1.89) bounds `T_k(X) 1` above; the relative
  stability is only in the complex direction `J` (the small first-order term `Delta`), not across different real
  regular backgrounds `U`. Writing `F_l(Y; V) = a_l (1 + h_l(V))` with `|h_l| < 1` on the analyticity domain needs a
  two-sided (relative) estimate of the labelled activity as a function of `V`, and its non-vanishing for complex `V`.
  Moreover, to be an R-term, `log(1 + h_l)` must satisfy the R-term bound, `<= e^{-p0(g_j)} e^{-kappa d_j(X)}`
  ([V] (1.100), [III] (2.31)). `F_l(Y_a)` contains the whole large-field activity of `Y_a`, whose dependence on the
  boundary field is not small in relative terms. Without the lemma, the only representation available is Balaban's
  own (1.104), in which released regions stay as multiplication operators `T_k(Y_i) 1` on large-field domains; labels
  would then be carried large-field domains again, which is exactly the divergent bookkeeping of REVIEW-2 G2.
* **Likely repair.** Factor the labelled activity as (unlabelled activity) times (conditional label weight given the
  region's boundary data), exponentiate the first as Balaban does, and prove a decoupling lemma for the second: the
  bare bubble's conditional weight depends on the scale-`j` field only through the background at bare resolution
  (curvature `~ eps_j L^{-2j}`) and through fluctuation integrals with decay, so its relative variation is small.
  Plausible, not routine, and it is the lemma REVIEW-2 G2 asked for.
* **Severity:** GAP (major: the G2 repair stands or falls with it). **Confidence:** high that the notes do not prove
  it; medium that the repair works.

### H2. Decoder: the conflict components are decided non-locally; their polymer representation is missing

* **Location.** `REVIEW2-RESPONSE.md` 1 ("the decoder output at a plaquette `q` is a function of `tau` on the union
  `U(q)`"; "each large-field region is enlarged by the `G`-components meeting it"); `WRITEOUTS.md` 1 step 1 ("a
  component inside `X'` is decided inside `X'`"); `S1-CURRENT.md` (F-a).
* **Claim.** The decoder is local per conflict component; Balaban's large-field regions are enlarged by those
  components and the rest of his machinery applies.
* **Failure.** Which sets form the component of `q` depends on `tau` outside `U(q)`: a positive-gain closed set `S`
  that touches `U(q)` and extends far away joins the component whenever `2|tau ∩ S| > |S|`, and `S` can be mostly
  outside any given ball. So the statement is false deterministically; what is true is `D(q) = D_r(q)` on the event
  `{U(q) ⊂ B_r}` (the global and the ball-restricted decoder agree), whose complement the Peierls sum bounds. That is
  enough for probabilities, not for Balaban's representation, which needs decompositions of unity that are products
  of local factors (his characteristic functions) so that `T` factorises over components of `Z` ([V] (1.70)-(1.72)).
  The indicator `{U(q) = U}` contains the constraint "no positive-gain set touches `U` from outside", a product over
  sets of unbounded size, and the indicator that two enlarged regions are separate components couples them. Neither
  is expanded anywhere.
* **Likely repair.** Mayer-expand the non-local constraint, `prod_S (1 - 1{g(S) > 0})`, as a hard-core gas of
  positive-gain sets with Peierls activities `(2 C_d)^u (c beta^{3/2} e^{-beta})^{u/4}`; the enlarged regions become
  polymers with these activities attached. Standard, but it has to be written, and `WRITEOUTS.md` 1 step 1 relies on it.
* **Severity:** GAP (fixable-looking). **Confidence:** high on the gap.

### H3. `S1-CURRENT.md` is a table of deltas, not the one-step induction

* **Location.** `S1-CURRENT.md` 1-4; `M1-PLAN.md` 0 (final verdict lists `S1-CURRENT.md` under "paper").
* **Claim.** The one-step bookkeeping for the current design, with the E-rows re-checked.
* **Failures.**
  1. **No order of constants.** `S1-PROOF.md` 5 had one; the current design adds `beta_min` for the decoder's Peierls
     sum, the layer cap `l_max` (which must be `>= C L + 1` for localised cores, see H5), the window, `r0 = c/L^4`
     (the old table says `c/L^2`), the margin `16 b' > 1`, and R10's `t_0`. I checked the obvious dependencies and found
     no circularity (`L`, then `r0`, then Balaban's `M, R_j, p0, kappa`, then `gamma0(L)`; `beta_min` is absolute; the
     enlargement cost `p0 (M R_0)^4 = polylog << beta_0`), but the brief's question cannot be answered from the note.
  2. **`Form_k` during the window is not stated.** Before release, a label is not a factor `a_l (1 + h_l)` but a
     constraint on unreleased bare variables inside `T_k(Z_k)` (the `tau'_k` part of the state is a function of
     them). (F-f) describes only the post-release form.
  3. **One E-row delta is missing.** Irregular coarse plaquettes created by Haar-random swallowed bonds
     (`SKETCH-STEPS.md` 1: "typically irregular") get no factor from [16] (71), because the coarse value is not an
     average of the weighted field; their cost must be attributed to the scale-`k` deep set's action
     (`beta_k r0^2 >> p0`). Similarly, (71) has to be applied to the filled field (whose action is not larger than the
     original's on the hole). Neither is in row 7.
  4. **Status drift.** `S1-CURRENT.md` 0 still says two points are sketch; `M1-PLAN.md` 0 calls it paper; the same
     section still lists "R4 for swallowed bonds: surjectivity plus compactness" and "the insertion of the
     footprint-weighted lifetime into [V] (1.80)-(1.85)" as sketch while the R2 and R4 rows say the opposite.
* **Severity:** GAP (the main induction is outlined, not written; G1 only partly resolved). **Confidence:** high.

### H4. R10 write-out: the large-field split and the probability conversion are not valid as written

* **Location.** `WRITEOUTS.md` 0.2 and 2 step D; `M1-PLAN.md` 0 (R10 row: "paper").
* **Claim.** Split by the event `E_D` (a large-field region at `L_*` joins `A` to distance `D/2`); on `E_D^c`,
  `log rho^{(t)} - log rho` is localised and Cauchy in `t` gives `e^{-kappa D/(2 L_*)}`; `P(E_D) <=
  e^{-c' p0^2 D/(M R L_*)}` "using Balaban's large-field factor per cube and his normalisation lower bound (R7)".
* **Failures.**
  1. **`E_D` is not an event of `(V_K, tau')`.** The large-field region at scale `K` includes unreleased regions
     created at earlier scales, which depend on integrated variables; for a fixed `V_K` the density is a sum over
     histories. "On `E_D^c`, `log rho^{(t)}` is ..." has no pointwise meaning. The correct form works on the extended
     space: `E[F|V] = E[F 1_{E^c}|V] + E[F 1_E|V]`, with the first term `(rho_{E^c}/rho) d_t log rho^{(t)}_{E^c}` and
     a final-scale cluster expansion of the remaining large-field polymers (Balaban's (1.104) regions as polymers) to
     make `log rho^{(t)}_{E^c}` a localised sum. This is doable but not written.
  2. **The probability conversion uses the wrong normalisation.** R7 (`CLOSE-OUT.md` 4) is a bare-measure bound with
     `O(1)` per bare site or flip. A scale-`K` cube holds `L^{4K}` bare sites, so R7 cannot turn Balaban's per-cube
     factor `e^{-c p0^2}` into a probability. What is needed is a ratio bound for the renormalised partition functions
     at scale `K` (forced large-field polymer versus free), `<= activity * e^{O(1) #cubes}`, from the convergent
     polymer representation. Not stated.
  3. **Smaller.** `F` is a polynomial in matrix entries, which is not gauge invariant; Balaban's removal of the
     gauge-fixing delta functions ([V] p. 378) needs gauge-invariant integrands, so the class must be the
     gauge-invariant polynomials (still dense in the invariant subspace). The constants depend on `L_*/l` (the number
     of steps carried) as well as on `(n, R/l)`. `|E[F|.] - f| <= 2` needs `|f|` bounded; it is `<= C(n, R/l)`.
* **Severity:** GAP (sketch-level, as M1-PLAN's own sketch list says; the "paper" mark in the R10 row is premature).
  **Confidence:** medium-high.

### H5. FILL / G6: the twist-free test, the layer cap, and the filling's uniqueness need re-statement

* **Location.** `FILL.md` 2-3 and its update; `REVIEW2-RESPONSE.md` 3.
* **Failures.**
  1. **The twist-free test is vacuous.** "Some loop of length `<= 8` in the complement that encircles a plaquette of
     `H_i`": the shortest loop around a single plaquette that avoids its four bonds is the `3 x 3` square, length 12.
     So the growth never starts from `H_0`, and `FILL.md` 1's own motivating example (the `3 x 3` loop with holonomy
     `~ theta`) is not caught. For slabs, loops around a `w x w` cross-section have length `~ 4(w + 2)`. The test must
     use loops in the boundary layer of the hole, of length up to the cross-section's perimeter. (This was in FILL
     before REVIEW-2; it was missed there.)
  2. **"Cap reached implies irregular `W`" is not re-proved for a layer cap.** The cap must be at least `C L + 1` so
     that localised cores always finish; for slabs the needed classification is "at regular `W`, an extended deep SO(3)
     structure is near-centre flux whose coarse loops enclose all of it or none" (FILL 0.2 gives this in effect, but
     it is not tied to the new rule).
  3. **Uniqueness.** The implicit function theorem gives a unique critical point in a small sup-norm ball, not the
     global minimiser. Define the filling as that critical point (measurable and deterministic), not as "the
     least-action configuration".
  4. **Owned bonds** for E7.J near a slab must lie outside the hole's Dirichlet data, otherwise the filling couples
     the coarse values; with a thin slab such bonds exist on every face, but it should be said.
  5. **Confusion of two objects.** `REVIEW2-RESPONSE.md` 3, "The Z2 part: a thin centre sheet has bare `tau = -1`":
     the SO(3)-deep sheets G6 is about are thick at the bare scale (`tau = +1`); a bare-thin sheet (`tau = -1`) is
     SO(3)-invisible and never excised. No consequence, but the bullet is wrong.
* **What holds.** The Dirichlet gap of a slab of thickness `w` is `>= 2 (pi/(w+1))^2` on the lattice, independent of
  the area, and the data bound `C r0 w <= C c L^{-3}` is small against it for `w <= C L`.
* **Severity:** FIXABLE. **Confidence:** high for 1 and 3, medium for 2.

### H6. N1 restatement (R7 for flipped sets) is wrong in detail

* **Location.** `REVIEW2-RESPONSE.md` 6 (N1), used by section 1's Peierls bound and `WRITEOUTS.md` 1 step 1.
* **Failure.** `f(P) <= |P|/6` is false: take all plaquettes containing a timelike bond between two fixed time
  slices; each such plaquette contains two of these bonds, all bonds are freed, and `f = |P|/3`. Soft modes also
  arise without freed bonds: remove all plaquettes at the four bonds of a plaquette `p0` except `p0` (20 plaquettes,
  `f = 0`), and 9 Gaussian directions become free. In both cases the Jensen route of `CLOSE-OUT.md` 4 fails because
  `<1 - tr U_p/2>_{-P} = O(1)`. The conclusion `poly(beta)^{|P|}` is plausible (each removed plaquette releases at most
  3 constrained directions, ratio `<= (C beta^{3/2})^{|P|}`), and that is all the Peierls sum uses, but it is not derived.
* **Severity:** FIXABLE. **Confidence:** high on the counterexamples.

### H7. Label bookkeeping: true conclusions, wrong intermediate statements

* **Location.** `WRITEOUTS.md` 1 steps 1, 2, 4 and "Uniformity".
* **Points.**
  1. "At least 4 bare flips per labelled skeleton bond": false at coarse vertices. With `B` the four positive-direction
     bonds at a coarse vertex, `sigma = d 1_B` has 12 plaquettes, needs 7 flips, and labels 4 coarse bonds (1.75 flips
     per label). Harmless: there is one vertex per cell, not `L^k` positions, so the factorised bound `prod a_b` should
     be per component, and the per-cell count is unchanged. (In the interior of a coarse bond, `d 1_B` for collinear `B`
     splits into separate one-bond components, so there is no chain discount there.)
  2. "Labels are created only during the first `O(window)` steps": false for large closed remainders, whose
     large-field regions are released after their shrinking time. Harmless (`e^{-beta |S|/2}`). The skeletons are
     nested, so no bond joins the skeleton at a later scale.
  3. Clusters meeting two labelled polymers give pair terms, and labelled polymers obey a hard core, so Step 4's
     closed form per coarse bond is approximate; corrections are higher order in `a`.
  4. The same action pays Balaban's large-field factors and the label suppression; the split must be stated (the
     exponent becomes `16(1 - delta) b`, `delta = O(p0^2 g^2 window)`, harmless).
  5. Step 1 bounds `a_b` by `e^{-16/g_j^2}` and step 4 uses `e^{-16/g_0^2}`; the difference is a `poly(g^{-2})` factor.
* **Severity:** NIT. **Confidence:** high.

### H8. Smaller points

* **NIT, decoder tie-break.** The decomposition over conflict components holds for a lexicographic order in a fixed
  plaquette order (I checked this), not for an arbitrary "fixed total order of `Z^2`" (`CLOSING.md` 1 (iii)). State
  the order.
* **NIT, outside M1 but argued by M1.** `REVIEW2-RESPONSE.md` 4's Wilson-loop formula uses the decoder output `tau'`
  (it differs from the raw `tau` by the filling) and needs `Hol_V(C)` regular, which fails for loops of physical size.
  5(c)'s density "by martingale convergence" ignores that the block fields with auxiliary noise do not form a filtration
  of the bare field, and that the decoder discards tie information (a `12 b > 1` count suggests this is negligible for
  Wilson loops, but it is not argued).
* **NIT, stale text.** `Assembly.lean` header and the `stepEstimates` row still cite TRAP, D-mod, P2', P4;
  `DECODER-LOCAL.md` 0 still states the withdrawn result above its update note; `FILL.md` 0.4-0.5 still describe the
  swallowed-bond surjectivity sketch.

## Status of the REVIEW-2 findings

| REVIEW-2 | status | comment |
|---|---|---|
| G1 no S1 for the current line | **partly resolved, still open** | `S1-CURRENT.md` names `Form_k` and the step order, but is a delta table without constants, window form or the noise/filling E7 delta (H3). |
| G2 labels in Balaban's form | **relabelled, still open** | Labels moved from "large-field region" to "R-term with an index", which removes the divergence only if `h_l` is small; that lemma is asserted (H1). R9's amendment (`tau = +1` dropped at scales `>= 1`) is consistent; at scale 0 `tau = -1` plaquettes must stay large-field (anti-confining SO(3) action), as the response implicitly keeps. |
| G3 decoder locality | **resolved for probabilities, open for the representation** | Packing, decomposition, shortest-chain Peierls bound and no-percolation are correct (see below). The use in Balaban's polymer representation needs the expansion of the non-local constraint (H2). |
| G4 hand-over | **relabelled** (points 1-3 to the interface, out of scope here); point 4 **addressed with new gaps** | WRITEOUTS 2 gives the `L^1` form; its split and probability conversion are not valid as written (H4). Complex weights: fine (see below). |
| G5 SU(2) encoding | **relabelled** to the interface (out of scope), agreed | The response's replacement formula is wrong for large loops (H8). |
| G6 extended holes | **mostly resolved, sketch level** | Layer cap and slab filling are the right repair; the twist-free test is vacuous as defined, and cap and uniqueness need re-statement (H5). |
| F7, N1, N2, N3 | F7 partly (rows renamed, still bookkeeping, stale headers); N1 restated with errors (H6); N2 resolved (withdrawn); N3 resolved (rate in EXTERNAL row 1, exponent `r >= 2` pinned) | |

## What I checked and found sound

* **Decoder as a packing.** For pairwise non-adjacent closed connected sets, `|tau + Sum S_i| = |tau| - Sum g(S_i)`;
  sets sharing only a cube merge into one component, which is itself a vertex, so the conflict rule (shared plaquette
  or cube) is right; the optimum is a maximum-weight independent set of positive-gain vertices, and it decomposes over
  connected components of the conflict graph, with gain and `|sigma|` additive and a lexicographic tie-break
  decomposing too. All sets containing `q` lie in one component. Deterministic and measurable in finite volume.
* **Peierls bound.** In a shortest conflict path, `S_i` and `S_{i+2}` share no plaquette, so each plaquette lies in at
  most two consecutive members; hence `|tau ∩ U| > |U|/4`, `U` connected, `|U| >= r`; the sum
  `Sum_{u >= r} (2 C_d)^u (c beta^{3/2} e^{-beta})^{u/4}` is volume-uniform and excludes wrapping and percolation for
  `beta_0` above an absolute threshold (given the per-flip bound of H6).
* **Piece-by-piece (1.97).** In [V] the activity bounds come from positivity of `T_k(X,(U,0))`, sup bounds and the
  first-order term `Delta` ((1.73)-(1.75), (1.89), (1.92)-(1.97)); no contour shift of the integration variables.
  Restricting by an indicator of integration variables (the label pattern, given H2) keeps each bound. The cluster
  expansion on the complement of the labelled polymers equals the full one minus the clusters touching them, and the
  touching terms are bounded by `C c1` per unit size (`c1 = e^{-p0}`), so they are local and small.
* **The count.** `b = 2 b_0 = 2 * 11 * 2/(48 pi^2) = 0.0929`, `16 b = 1.486`, `12 b = 1.115`; `d L^k` skeleton bonds per
  scale-`k` cell; the minimal remainder `d 1_b` (6 plaquettes, 4 flips with absorb-on-tie); per-cell label activity
  `e^{-16/g_k^2} L^{(1-16b)k} poly` decreasing in `k`, vanishing per `L_*` cell as the spacing goes to zero (any
  `e^{polylog(g_0^{-2})}` prefactor is beaten by `L^{-0.49 K} = e^{-c g_0^{-2}}`). Skeletons are nested.
* **Slab gap.** Area-independent Dirichlet gap; data small against it for `w <= C L`.
* **Complex weights in the conditional step.** `Exact.lean`: `resample = w * N/D` with `D` the fibre integral of the
  positive reference kernel `w`, not of the term. At fixed `w`, `D`, `Reg` and history index, `resample` and the
  pushforward are linear in `(I, N)`; splitting a bounded complex density into four non-negative parts gives
  `map_resample_eq` for complex `I`. Conditions to state: `w`, `Reg`, the history sum independent of `t`, and
  `|e^{tF}| <= e^{|t|}` for integrability.
* **R10 insertion.** `E[F|V_K, tau'] = d_t log rho_K^{(t)}|_{t=0}` is an identity of laws; `t_0` depends on `n`, `R/l`
  and the coupling at physical scale `l` (fixed as the spacing goes to zero); the number of steps `K - m` is fixed;
  gauge-invariant local insertions generate no relevant terms besides constants.

## What I could not check, and why

* Balaban's papers line by line beyond the passages listed; [III] (2.31) is partly illegible in the text layer (I used
  [V] (1.100) for the R-term bound).
* Whether `h_l` is in fact small (H1): this needs the decoupling estimate, which does not exist yet.
* The Lean files were read, not rebuilt; scripts and logs were not re-run. BYPASS, OFFCENTRE, R2-REPAIR and the other
  pieces unchanged since REVIEW-2 were not re-reviewed.
