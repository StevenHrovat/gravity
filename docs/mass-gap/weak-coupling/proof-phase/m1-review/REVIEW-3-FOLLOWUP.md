# REVIEW-3 follow-up: part 1 of the response (N-1, H5, H6, H1, H2), 2026-11-22

Read: `../m1-tools/REVIEW3-RESPONSE.md` (all), the update notes it names (`DECODER-LOCAL.md`, `FILL.md`, `CLOSING.md`,
`CLOSE-OUT.md`, `S1-CURRENT.md`, `WRITEOUTS.md`, `M1-PLAN.md` 0, by their update paragraphs and the changed rows).
Source checked: [V] (CMP 122, 355-392), text layer extracted with `pdftotext` (layout and raw modes), pp. 377-380 and
387-391. H4, N-2, H3, H7, H8 are not judged here (part 2). Nothing was built or re-run.

## Verdict

Part 1 is a real improvement. N-1, H5 and H6 are resolved. H2 is resolved by changing the blocking, which is the right
move. H1 is no longer at risk of being fatal: the new form (labels as positive fixed-domain factors) no longer needs a
two-sided bound across real backgrounds. But the H1 repair goes further than the text it cites. Balaban's fixed
domains in (1.103)-(1.104) stay large-field domains and take no part in later steps, while released labelled domains
are integrated over in later small-field fluctuation integrals. That step is a new adaptation of [I]/[II] and needs a
small factor per domain. The "paper" mark for H1 should be "citation-level adaptation, with three fixable points". No
FATAL findings; one GAP (H1, reduced).

## Answer to the author's question: is the first-order bound before (1.73) per `M R_k`-cube or per component?

**As printed, it is a single bound for the operation `T_k(X)` of the whole component, with no size factor.** [V]
p. 379: in (1.71) only the quadratic form in `B` and the term `V(X~)` depend on `(U, J)`. The first-order term of the
quadratic form "can be bounded by" `O(1) B^{3/2} A^{1/2} |p(g_k)| |R_0| (alpha_{0k} + alpha_{1k}) <
O(1) B^{3/2} A^{1/2} C_0 M^d R_k^{d+2} p^2(g_k) q0(g_k) g_k`, "and this bound is small". (The symbol `|R_0|` is
partly illegible.) For `V(X~)`, the expansion "creates a connection between their localization domains and the set
`B_0 ∪ (...)`", the terms are resummed, and "the resummed expression has the same bound as above, with a different
constant `O(1)`". Then (1.74)-(1.75) use `sup|Delta|` with no factor of `|X|` or `d_k(X)`, and the remark after (1.92)
"estimated ... in (1.73) by 1".

**Caveat.** `M^d R_k^d` is the volume of one `M R_k`-cube, and a first-order term in variables spread over all of `X`
would normally be extensive. The printed uniform bound is consistent only if `(U, J)` couple near a set of bounded size
(the set `B_0 ∪ (...)`; its definition is not legible in the scan) or if released components have bounded size. I
cannot settle which from the text. **Recommendation:** keep the case split. It is correct under either reading, and it
is cheap since `delta_k -> 0`. Set its threshold as in H1.2 below, not at `1/4`.

## Status of each item

### N-1 (small field at scale 0): **resolved**

* The exact rewriting checks. Given the bare SO(3) field, `tau` is a Z2 gauge theory with couplings
  `J_p = (beta/2)|tr U_p|`. A centre multiplication on `B` flips `tau` on `d 1_B` and multiplies the weight by
  `exp(-beta Sum_S |tr U_p|) = e^{-2 beta |S|} exp(beta Sum_S (2 - |tr U_p|))`. Since `2 - 2|cos(phi/2)| ~ phi^2/4` and
  the normal term is `beta phi^2/8`, the net SO(3) action on `S` is inverted to `+beta phi^2/8`.
* So `tau = -1` plaquettes cannot be SO(3) small field at scale 0.
* The rule "SU(2)-regular at scale 0, SO(3)-regular from scale 1" fixes this. A flip has `|U_p - 1| > sqrt 2` in
  operator norm, so it lies in `P_0` in every term. The split `delta = p0^2/beta` of its action is right.
* No new problem: in small-field regions Balaban's Lie-algebra average commutes with `Ad`, so the scale-0 step to an
  SO(3) block field is Balaban's step there.

### H5 (twist-free test, cap, filling): **resolved** (one step honestly marked sketch), two NITs

* **The test is no longer vacuous.** Loops in the shell `O(H)` of length up to `lambda = 8(l_max + 2)`, with threshold
  `C_tw r0 |gamma|^2`. A loop that bounds inside the shell passes by non-abelian Stokes (area `<= |gamma|^2/16`, each
  plaquette `< r0`). The `3 x 3` loop and the transverse slab loop `4(w + 3)` are both in the shell.
* `l_max = C_1 L >= C L + 1`, the implicit-function definition of the filling, and owned bonds outside `O(H)` are all
  correct.
* The corrected Z2 bullet is right.
* **NIT 1.** In item 2, a failing loop gives `theta > C_tw r0 |gamma|^2`, not `> C_tw r0 lambda^2` (`|gamma| <= lambda`).
  The conclusion survives: `|gamma| >= 12` for a linking loop gives `theta > 144 C_tw r0`, and `r0` is fixed while
  `eps_{k+1} -> 0`.
* **NIT 2.** The new threshold lets the data around the hole deviate from pure gauge by up to
  `C_tw r0 lambda^2 ~ 64 C_tw C_1^2 c L^{-2}`, not `C c L^{-3}` as `FILL.md` 3 still says. The Dirichlet gap is
  `~ 1/(4 C_1^2 L^2)`. Both scale as `L^{-2}`, so it closes if `c <= c'/(C C_tw C_1^4)`, with `c` (in `r0 = c/L^4`)
  chosen after `C_1` and `C_tw`. Redo the numbers in `FILL.md` 3 and the `||E|| <= C L^2 r0` of E7.J, and put this
  order into H3's constants list.

### H6 (per-flip normalisation): **resolved** at citation level

* The false claim is withdrawn.
* The exponent count is right: one plaquette removes at most 3 rows, the gain is `C beta^{1/2}` per freed direction,
  and a fully freed bond gives `beta^{3/2}`, consistent.
* The ratio is cited from Balaban's two-sided bounds, with the removed region treated as a large-field region. Fine as
  a citation. It gives `poly(beta)` per flip, possibly with a larger power than `3/2` once the supporting bonds are
  counted, which the margins absorb.
* Since the decoder no longer needs the Peierls sum for locality (H2), R7' now matters only for the label count (P3)
  and the fidelity estimate.

### H1 (labels): **relabelled into a sound form; still open at reduced severity (GAP)**

What is right:
* Splitting `T_k(X) = Sum_l T^l_k(X)` at release, before the Mayer expansion, is legitimate, because `1_l` is a
  function of `T`'s own integration variables (given H2).
* `Phi_l = T^l_k(X) 1 > 0` for real configurations.
* The relative stability of `T^l` in Balaban's complex variables follows from his positivity argument
  (1.73)-(1.75) with `F = 1_l`.
* The upper bound (P3), including (1.89) improved by `d_k(X)`, is right.
* Not exponentiating removes the need for `h` small across real backgrounds. That was the core of REVIEW-3 H1.

What does not yet follow:
1. **(P2) is stated for the wrong variables, and 4.3 contradicts 4.4.** 4.3 says "real backgrounds are never
   compared". Yet 4.4 compares `Phi_l(U_bg e^{igB})` with `Phi_l(U_bg)` for a real fluctuation `B`, which is a real
   variation. What covers it is Balaban's expansion in `A'` (the deviation from a regular base, real or complex, within
   `alpha_{0k}`), not the `J` directions alone. State (P2) on the whole analyticity domain `U_k(X, alpha_0, alpha_1)`,
   and check that Balaban's fluctuation bounds put `g_k B` inside it (`g p(g) <= alpha_{0k}`, his choice of `q0`).
   FIXABLE.
2. **The later-step use is not Balaban's (1.103).** In (1.104) the fixed domains `Y_i` are second-class
   (large-field) components. Balaban says their functions depend only on `V_k` restricted to `Y_i`, "therefore they do
   not participate in operations connected with next renormalization transformations". A released labelled domain is
   small field at the next step, so its variables are integrated in the next fluctuation integral with the factor
   `1 + eta(B)`. That is an extension of the cluster expansion of [I]/[II], not a citation of (1.103).
   Moreover, Balaban's fixed-domain expansion uses a **small** factor per fixed domain. The (1.103) remark replaces
   "the first product over h" by a product of factors `eps^3` (OCR "e3") over the `Y_i` inside `X'`. In (1.93) the
   smallness `eps^{1/3} <= exp(-(1 + beta) 2d)` produces the decay factors linking domains. `|eta| <= e^{1/4} - 1 ~ 0.28`
   is not of that kind. **Repair:** take the threshold `delta_k |X| <= eps_*`, with `eps_*` as small as Balaban's
   `eps`. Since `delta_k -> 0` this only moves the case split. Then write the fluctuation-integral step with
   fixed-domain factors as a lemma. GAP (smaller than before), medium confidence that this is all that is needed.
3. **`Phi_l ∘ U_bg` is not a function on a fixed domain.** Balaban's background is non-local (exponentially decaying
   dependence through the H-functions), so after one step the factor depends on `V_{k+1}` everywhere. It needs a
   localisation, for example by writing `log Phi` differences between the full and the localised background through
   (P2)'s stability per analyticity ball, with the decay of [15] (190). Not mentioned. FIXABLE.
4. **Carrying large components "at most doubles Balaban's lifetime ... absorbed in his constants" is not a
   citation.** (1.80)-(1.88) are proved for `K <= n0 - j + R_j`. Extending this needs his entropy induction re-run, as
   for R2's footprint-weighted lifetime. Mark it sketch, not citation-level.
5. **NIT.** "`|X_{k'}|` shrinks by `L^{-4}` per step" holds for bulky components. For thin labelled ones (tubes,
   sheets) it is `L^{-1}` or `L^{-2}`. The sums stay geometric, so nothing changes.

### H2 (decoder): **resolved**; one new minor problem

* **Resolved.** Decoding per connected component `C` of the union `D_0` of scale-0 `M R_0`-cubes that contain a flip
  is local, deterministic and measurable. `C` lies in one component of `Z_0`, since every flip cube is in `P_0` by N-1
  and `Z_0` is the `M R_0`-cube cover. So the output is a function of that component's `T`-variables. The output is
  closed, and the label count is unchanged (each chosen set still has `> 1/2` flips). The lexicographic tie-break
  decomposes.
* **New minor problem: the fidelity argument is false.** The response says that sets leaving `D_0` "have an unflipped
  stretch longer than `M R_0` outside the flip cubes". This does not follow. A chosen set must lie inside `C`, but its
  unflipped plaquettes (up to half) can poke a single plaquette into a flip-free neighbouring cube.
  * Example: the minimal bubble `d 1_b` around a bond `b` on a face of the cube grid, with its 4 flips in one cube and
    an unflipped plaquette in the next. It is not chosen, so the label is lost.
  * The loss is therefore a fixed fraction of order `1/(M R_0)` of the minimal labels. It may be most of the skeleton
    labels, if the `M R_0` grid is aligned with the block lattice, since skeleton bonds then lie on the cube grid's
    faces and edges.
  * The law and every upper count are unaffected. This matters only for N-2 (what the block state still records).
  * Possible fixes: let `D_0` be the flip cubes plus one layer of neighbouring cubes, which keeps locality inside the
    `Z_0` component only if Balaban's large-field cover includes that layer. Or accept the loss and say so in N-2.
  * NIT for M1; medium confidence on the alignment remark.

## Findings, one line each

* **GAP (H1, reduced):** released labelled domains enter later small-field fluctuation integrals as factors
  `1 + eta`. This is an extension of [I]/[II], not Balaban's (1.103)-(1.104), where fixed domains stay large-field. It
  needs a small factor per domain (threshold `eps_*`, not `1/4`), (P2) on the full analyticity domain (real `A'`
  included), and a localisation of `Phi ∘ U_bg`. Carrying beyond the lifetime is sketch, not citation.
* No FATAL findings. NITs: the H5 inequality direction and the data-bound constants order; the H2 fidelity claim; the
  thin-component shrink rate.

## Follow-up 2 (part 2 of the response and the new labels repair), 2026-11-22

Read: `../m1-tools/REVIEW3-RESPONSE.md` 6-12 (all of part 2 and the labels sections 11-12), `S1-INDUCTION.md` (all),
`M1-PLAN.md` 0 (the new verdict). Source checked: [I] (1.11)-(1.12) (the analyticity domain, text layer, raw mode) and
[III] p. 261 ((2.34)-(2.39)). Nothing was built or re-run. Commit ids were not checked (no git).

### Verdict

The remaining GAPs are closed at the level the notes now claim. I found no FATAL error and no new GAP. The one-step
induction is now written as an induction, with its constants in order. R10 is redone on Balaban's positive
representation with a scale-`K` normalisation that works. The labels have a clean form: a constant times `exp` of a
local term with no linear coupling, contracting by `C L^{-4}` per step. The density argument in the OS norm is a sound
idea, correctly marked sketch. What remains is FIXABLE or NIT, listed below. The verdict in `M1-PLAN.md` 0 is
essentially accurate; I would amend it in three places (last subsection).

### H1 (labels, sections 11-12): **resolved**, at the stated level, with NITs

What checks:
* **Persistence rule (12.1).** The skeletons are nested, so a remainder appears in `tau'_j` exactly for
  `j <= j(S)`. A remainder with `j(S) = 0` changes no coarse bit and can be summed into the released history. Summing
  a label out at the step past `j(S)` is exact, because its index stops being a variable of the law. Upper counts only
  decrease.
* **Form at release (11.1).** `Phi_l = a_l e^{L_l}` with `L_l(flat) = 0`. The no-linear-coupling lemma (R8) applies
  because `L_l` is gauge invariant and analytic at the flat configuration. This is now derived from the stability
  bound (P2) plus R8, not asserted.
* **Contraction lemma (12.2).** I followed it step by step.
  * A term localised at one scale-`k` box with no linear part contracts by `L^{-4}` per step, because background
    curvature in scale-`k` units is `L^{-2}` times the coarse curvature. A point term is irrelevant, while a bulk `F^2`
    density summed over a block is marginal.
  * There is no term linear in `F_bg`: the R8 lemma applies to the whole new gauge-invariant `L^{(k+1)}`, so the
    cross term vanishes in total.
  * The dependence of the fluctuation covariance on the background enters only at order
    `N_k (g_k/alpha_1)^2 L^{-4}`.
  * Iterating gives a total weight drift `e^{O(eps_*)}`, independent of the label's lifetime. This removes the
    linear-in-`K` problem of follow-up 1.
* **Constant into `a_l`, not into the coupling (11.5).** Correct. A position-dependent `F^2` would not be covered by
  [I] Theorem 2, and the label's own constant does not touch the bulk running.

NITs:
1. **Tails.** The localisation tails "add `C e^{-kappa} N_k` ... absorbed into `C`". They carry no `L^{-4}`, so
   `theta = C L^{-4} <= 1/2` needs `e^{-kappa} <~ L^{-4}`, that is `kappa >= 4 log L + C`. Balaban allows `kappa`
   large given `L` ([III] p. 260), but the condition belongs in `S1-INDUCTION.md` 1, row 5.
2. **Multi-cube components.** The lemma assumes the label term is localised in one box. A released component spanning
   several cubes contracts only once its image is below a cube. Before that the step is marginal: bounded by
   `1 + C N_k + C e^{-kappa}`, for `log_L(size)` steps. The threshold `eps_*` keeps the drift `e^{O(eps_* log size)}`.
   This should be said.
3. **The reading of [V] p. 379 (sketch point 3), half settled.** [I] (1.11)-(1.12) define the analyticity domain
   as `U = U' U''`:
   * `U'` is G-valued with `|dU' - 1| <= alpha_0`, and per cube of size `O(1) L M` it is gauge equivalent to
     `exp(iA)` with `|A|, |grad A| <= O(1) L M B alpha_0`;
   * `U'' = exp(iA'')` with `A''` in the complexified algebra, `|A''|, |grad A''| <= alpha_1`.
   
   The printed first-order bound before (1.73) carries the factor `(alpha_{0k} + alpha_{1k})`. That supports the
   response's reading: the expansion covers deviations of the real base of size `alpha_0` as well as the complex part.
   So taking the flat configuration as base, patch by patch, is consistent with the per-cube distance
   `O(1) L M B alpha_0`. If the expansion turns out to cover only `alpha_1`, chain through `O(L M B alpha_0/alpha_1)`
   balls per cube: the drift is still `O(polylog) delta_X`, far below `eps_*`. Either way the conclusion stands. The
   per-cube versus per-component question remains as answered above.
4. **"Citation-level adaptations".** Three of the inputs in 11.6 are not citations but claims that Balaban's proofs
   carry over with a change:
   * (P2) on the full domain;
   * the localisation of `L_l ∘ U_bg`;
   * small-field steps that accept an indexed, non-covariant local term whose constant is moved by hand.
   
   They are plausible and named, but they are unchecked adaptations. The verdict should call them that (see below).

### H3 (the induction, `S1-INDUCTION.md`): **resolved**, one FIXABLE point

* **What resolves it.**
  * The constants table has no circularity I could find: `L`, `C_1, C_tw`, `r0`, Balaban's constants, `beta_min`,
    then `gamma0(L)` last, with `t_0` per observable.
  * `Form_k` includes the window form (unreleased labels as indicators inside `T`) and the label sum as a hard-core
    polymer sum.
  * Each of the eleven operations has its level.
  * The new E-row 7c attributes the factors of coarse plaquettes meeting a hole to the deep plaquette's own action. It
    uses the true configuration's action, not the filled field's, and the attribution count `6 (2 C_1 + 5)^d` is right.
* **FIXABLE: 7c pays only the first generation.** Irregularity created by Haar noise on swallowed bonds, or by a
  filling whose curvature lies between `eps` and `r0`, can persist at later scales of the same region's life. At scale
  `k + 2`, [16] (71) again does not apply, because the scale-`(k+1)` field in the blocks is the noise or the filled
  field. Those factors must also be attributed to the original deep set. The budget suffices:
  `r0^2/(8 g_k^2) ~ g^{-2}` against `R_k * C(C_1) p^2 = polylog`. State condition 8 as
  `r0^2/(8 g_k^2) >= C(C_1) R_k p(g)^2 + p(g_k)^2`, and say that 7c applies at every scale of the region's life.
  Medium confidence that later generations occur at all, but the fix is free.
* **NIT.** Add `kappa >= 4 log L + C` (H1 NIT 1) and `eps_* <= L^{-4}/(2C)` with `C` after `kappa` in the order.

### H4 (R10 on the positive partition, section 7): **resolved**, one FIXABLE wording point

* **What resolves it.**
  * The mixture formula `E[F|V,tau'] = Sum_G P(G|V,tau') d_t log rho_G` is correct for non-negative `rho_G`.
  * The `L^1` estimate splits cleanly into a local part and `P(G crosses)`.
  * The scale-`K` normalisation now works. The upper bound uses Haar `<= 1` on `G`'s region. The lower bound
    restricts `Z` to small fields on that region, using the positivity of all terms, and gives
    `exp(O(1) (M R_K)^d log g_K^{-2})` per cube. This is paid from the per-cube large-field budget
    (`p0 >> M^d R^{d+1} >= (M R)^d log g^{-2}`, since `R >= log g^{-2}`).
  * The "one more step" argument is legitimate: the induction hypothesis at scale `K` must allow the step
    `K -> K + 1`, whose normalisation is exactly this. Say so explicitly.
* **FIXABLE: positivity and the Mayer expansion are mixed.** "The large-field domains ... with their attached boundary
  terms Mayer-expanded into connected clusters ... form a polymer configuration with non-negative activities" is false
  as stated: Mayer activities `e^{B'} - 1` are signed.
  * The argument needs only `rho_G >= 0`. That holds if `G` is defined before any Mayer expansion: from the
    large-field domains `Y_i` and the labelled domains of a term of (1.104), with the boundary terms kept in the
    exponent as part of each term's (real) action.
  * Mayer-expand only inside the ratio `Xi_{-G}/Xi`, which need not be termwise positive.
  * Also note that at fixed `V` the top-scale characteristic functions fix the top large-field set, so the "gas at
    fixed `V`" is a sum over earlier unreleased regions and labels under a fixed constraint. Harmless, but it is the
    accurate statement.
* **NIT.** With real `t` only, "Cauchy in `t`" is used for the analytic local terms `Phi_t(X)`, which are analytic in
  complex `t`; the measure is never tilted by complex `t`. One sentence.

### H2 side remark (labels lost near the scale-0 grid): **resolved by moving it to N-2**

* The false fidelity claim is withdrawn (11.7).
* Lost labels are local structures: a lost minimal bubble is a sign flip of one bond. Given the block state they are
  local noise, handled by the conditional decorrelation of section 8. Closed sets large enough to link `C` and
  `theta C` are crossing terms.
* Nothing in M1's law or counts used fidelity.

### N-2 (density in the OS norm, section 8): **new argument, sound in outline, correctly marked sketch**

* **The idea is right.**
  * `||.||_OS <= ||.||_{L^2}`. The spectral upgrade needs density in the OS norm only.
  * `||F - f_l||^2_OS` splits by the law of total covariance into a conditional covariance of observables `2t` apart
    and `E[E[theta R|G] E[R|G]]`. The second is bounded by `C ||E[F|G] - f_l||_{L^1}` without any measurability of
    `theta f_l`.
  * Sub-`l` vortices linking only `C` decorrelate; those linking both `C` and `theta C` are crossing terms.
  * So the question of `c0` against `1/b` is avoided. That is a genuine improvement on the REVIEW-2 follow-up's
    concern.
* **NIT (wording).** "`f_l` drops out, being `F_l`-measurable": only `f_l` drops out. `theta f_l` is not
  `F_l`-measurable, because the blocking is not reflection covariant (lexicographic tie-breaks, noise, and the scale-0
  grid unless the plane is a grid plane). The term `Cov(theta f_l, F | F_l)` is a conditional covariance of two
  observables `2t` apart and is bounded by the same decorrelation. No consequence.
* **What is sketch (named in `M1-PLAN.md` 0 item 4, agreed).**
  * Conditional decorrelation for **bounded fine** observables, uniformly in the spacing. Section 7's insertion
    cannot be used for them, since `t_0` would depend on `a`. It needs the fine observable treated as a fixed
    large-field insertion in Balaban's representation at every scale below `l`.
  * The uniform polynomial approximation of `f_l`.

### Is the verdict in `M1-PLAN.md` 0 accurate?

Essentially yes. It no longer claims completeness, it names five sketch points, and the levels match the notes. Three
amendments:
1. **Name the adaptations.** "Labels: paper on citation-level adaptations below `eps_*`" should name the three
   adaptations of 11.6 (H1 NIT 4) as unchecked carry-overs of Balaban's proofs, as a sixth item or under item 3. The
   same applies to "R10: paper on citation-level inputs" for the one-more-step normalisation.
2. **Sketch point 3 is half settled.** [I] (1.11)-(1.12) and the factor `(alpha_0 + alpha_1)` support the reading of
   `A'` (H1 NIT 3). The per-cube versus per-component question stays open, and the case split is kept.
3. **Add the FIXABLE items to the to-do list.** 7c's attribution at every scale of the region's life (budget with
   `R_k`); the conditions `kappa >= 4 log L + C` and the multi-cube contraction remark; and the positivity of `rho_G`
   defined before the Mayer expansion in R10.

### Findings, one line each (follow-up 2)

* No FATAL, no GAP.
* FIXABLE: S1-INDUCTION 7c must attribute factors at every later scale of the region's life (condition 8 with a
  factor `R_k`).
* FIXABLE: R10's "non-negative activities after the Mayer expansion" is false as worded; define `G` before the Mayer
  expansion.
* NITs: the contraction lemma's tail condition `kappa >= 4 log L + C`; marginal steps for multi-cube components; the
  `theta f_l` wording in N-2; Cauchy in `t` only for the local terms; the verdict should call the label inputs
  adaptations, not citations.

## Follow-up 3 (Lemma UV-TV (i), `UV-TV.md`, `REVIEW3-RESPONSE.md` 13-14), 2026-11-22

Read: `../m1-tools/UV-TV.md` (all), `REVIEW3-RESPONSE.md` 13 and 14, and the Lean one-box layer as far as its
hypotheses go (`formal/ProofPhase/OneBox/Criterion.lean`: `abs_cov_le_of_oneBox`, `OneBoxSum`; `Restricted.lean`:
`IsInfluenceBoundOn`). Nothing was built or re-run.

### Verdict

The diagnosis is right, and the repair points the right way, but both need sharpening.
* **(b)** The one-box Lean hypothesis, a bound for every boundary configuration, cannot be verified for this kernel,
  but not for the reason given: the sliding vortex example does not produce an influence of order `|J|`. The real
  reason is that large-field boundaries lie outside any control: Balaban gives only upper bounds there, and the box law
  may be multimodal. No choice of box size or influence metric removes this.
* **(a)** The block estimate is right in order. The decay rate is wrong by a power, harmlessly.
* **(c)** The good/bad route is sound in principle. But its stated hypothesis, domination by a subcritical
  *independent* percolation, is not available: badness is inherited from neighbours. The usable hypothesis is an
  *annealed* Peierls bound on bad sets under each of the two coupled measures.
* **Lemma UV-TV (i) as stated in 13.4 is false.** It cannot hold uniformly in the coarse field: a coarse large-field
  region joining `B` to distance `r` carries disagreement through with probability 1. It must be restated with the
  coarse bad set in the failure event. Then the composition (ii) is a multi-scale percolation estimate for Balaban's
  history regions, not a routine union bound.

No FATAL finding; two GAPs in the plan (below).

### (b) Is it a real obstruction? Could other boxes or another influence notion meet the hypothesis?

* **What the hypothesis asks.** `IsInfluenceBoundOn` quantifies over all boundaries `sigma`, all values `s` at `z`,
  and all admissible (gauge-invariant, boundary-frozen) `F` with per-site oscillation `<= L`. `OneBoxSum` weighs
  `kappa(u)` by `e^{lambda E^(u)}`, with `E^(u)` the distance from `u` to the **far** side of the box.
* **The example does not give influence `~ |J|`.**
  * A vortex sheet is codimension 2 in 4D and a monopole line codimension 3. Since the test functions are gauge
    invariant, only the cores count: moving a sheet changes `~ l_B^2 w^2` core sites, not `l_B^4`.
  * At low temperature a 2D membrane in 4D is rigid. Changing one site where it meets `dJ` bends it locally, rather
    than redistributing its position across the box.
  * Even with an `O(1)` total-variation shift per site, the sites that matter lie along a curve of length `~ l_B`. The
    sum is then `~ l_B^3 << gamma l_B^4` for large boxes.
  * So, as stated, (b) is not shown; bigger boxes would beat that particular mechanism.
* **Why the sup still cannot be verified.** For boundaries or coarse data that are large field near `J`, nothing
  controls the box law. Balaban's large-field analysis gives only upper bounds (positivity, `T(1)`). Large
  chromomagnetic backgrounds can have unstable fluctuation directions (the Nielsen-Olesen instability; compare the
  charged quartic mode of `MILESTONE-1.md`), so the box law may be multimodal, and a single site may tip it between
  modes. An influence bound for every `sigma` would need a theory of the kernel in exactly the regime where none
  exists. That is the obstruction. It should be stated this way, and the sliding-sheet example dropped or demoted to
  an illustration.
* **Other boxes: no.** Box size cures (a) and the codimension-2 example, not the absence of control.
* **Another influence notion: no.** A Wasserstein (Kantorovich) Dobrushin criterion with distances scaled by `g_j`
  would handle the Gaussian part even single-site, followed by one smoothing step to reach total variation. But a
  boundary value can jump by `O(1)` in a large-field direction, so the worst case is unchanged.
* **Restricting the state space: no.** Restricting single spins to small-field values satisfies the sup trivially but
  changes the measure. The total-variation cost of the restriction over a region of `(R/a)^d` sites does not vanish
  (large fields are dense in physical units at fine scales), so it must be paid locally, through a percolation of bad
  regions. That is (c) again.
* **Conclusion:** good/bad is the right structure, but it is a new theorem, not a hypothesis change to `theoremA_on`.
  Dobrushin-Shlosman's oscillation iteration is worst-case by construction.

### (a) The block estimate

* **Single site fails, agreed**, for two reasons:
  * the influence `~ eps_j/g_j = p(g_j)` in total variation;
  * the kernel is a **fibre** measure (`block(V_j) = V_{j+1}` fixed), so a single fine site cannot move alone. Its
    one-site specification is degenerate.
  
  Boxes must therefore be unions of `L`-blocks, so that the block constraints are internal to the box. Say so.
* **The order `k_J(z) <~ (log p/m)^d` is right**, with one correction to the coupling. A shift coupling makes every
  site differ. Use a sequential or maximal coupling: the Hamming-Wasserstein distance is
  `<= Sum_r #(sites at distance r) * TV(marginals beyond r)`, with the far-marginal total variation
  `<~ p(g_j) e^{-m r} r^{(d-1)/2}` (massive covariance). This gives the stated order.
* **The rate is off by a power.** In `OneBoxSum`, `E^(u) >= l_B` (distance to the far side), so the weighted sum is
  at least `e^{lambda l_B} Sum k`. With `l_B ~ C (log p/m)^{d+1}/gamma`, the rate is
  `lambda ~ 1/l_B ~ gamma (m/log p)^{d+1}`, that is about `m^{d+1}/(log log g_j^{-1})^{d+1}`, not
  `m/log log g^{-1}`. This is harmless for (ii), since `t/l -> infinity` beats any power of `log log`. Correct it in
  `UV-TV.md` 2 and 6.
* **Not finite range.** The specification has exponentially decaying interactions (E-terms, the non-local
  background), not finite range. The weighted sum already allows that; the percolation version (c) must too.

### (c) Is the good/bad Theorem A sound, and what exactly must its percolation input be?

* **Sound in principle**, as a Peierls-plus-Dobrushin coupling argument. But the hypothesis "the bad set is dominated
  by a subcritical **independent** percolation" is not available.
  * Badness is inherited: a bad neighbouring box makes the boundary of `J` bad with probability close to 1. So there
    is no bound `P(J bad | revealed neighbours) <= eta`.
  * Without such conditional bounds or finite-range dependence, domination by a product measure
    (Liggett-Schonmann-Stacey) fails, and van den Berg-Maes's sequential argument does not apply as stated.
* **The usable hypothesis (annealed Peierls, per copy).** For each of the two measures to be coupled, and every
  connected set `A` of boxes, `P_i(every box of A is bad) <= eta^{|A|}`.
* **The argument with it.**
  * Explore from the region where the boundary conditions differ. Decide each box's goodness before coupling it,
    from its already revealed boundary.
  * Couple good boxes with the influence bound and bad boxes arbitrarily.
  * Then `P(a disagreement path through boxes b_1..b_n) <= E[Prod_i (k + 1{bad_i})]`, a martingale product with each
    `bad_i` measurable before step `i`.
  * This is `<= Sum_{A ⊂ path} k^{n-|A|} P(bad on A in copy 1 or copy 2)`, and
    `<= Sum_A k^{n-|A|} 2^{|A|} eta^{|A|/2}`: split `A` between the copies and use `min(P_1, P_2)`.
  * Summable for `k`, `eta` small. Only marginal (annealed) bounds per copy are used.
* **Two further requirements.**
  * **Good must be a property of the pair of boundaries.** The influence bound is applied along interpolations
    between the two copies' boundaries, and a hybrid of two small-field boundaries can be large field if they sit in
    different gauges. Define good as: both small field on the boundary layer, and within `C eps_j` of each other in a
    common gauge. Otherwise the box is bad.
  * **The coupling must be modulo gauge**, with a measurable gauge choice box by box (axial, rooted consistently),
    since only gauge-invariant `F` are tested. The Lean admissibility layer handles gauge for the oscillation
    iteration, not for couplings.

### Is the rarity of bad boxes given the coarse field available uniformly, or does it hide the same problem?

* **Not uniformly. Lemma UV-TV (i) as stated is false.** 13.4 asks for the coupling "uniformly in `j`, in the volume,
  and in the field outside the neighbourhood", for all `V_{j+1}`. If `V_{j+1}` has a large-field region joining `B`
  to distance `r` (allowed, since the agreement is only on the `r`-neighbourhood), the fine kernel inside it is
  uncontrolled, and disagreement can pass with probability 1. `UV-TV.md` 3.2 says as much ("bad by fiat; rarity from
  the coarse law one scale up").
* **It does not hide the same problem if everything is annealed.**
  * (A) and (B) of 13.4 are averages over the block state: an `L^1` norm and an expectation of a conditional
    covariance. So failure events may depend on the coarse data, as long as their probability under the law is small.
  * Restate (i): the two `V_j` agree on `B` except on an event contained in "a bad region of either copy (fine bad
    boxes at scale `j`, or the coarse large-field set of `V_{j+1}`) joins `B` to distance `~ r`", plus the
    good-region contraction tail.
  * For (A), the comparison configuration must itself be sampled from the law: an independent resample of the far
    coarse data given `H`, not an arbitrary `F'`. Then annealed bounds apply to both copies.
* **The input this needs: a multi-scale crossing estimate.** Under the law (and under the law conditioned on `H`, for
  the resampled copy), the probability that Balaban's history large-field region, the union of large-field sets over
  all scales `<= l` connected across scales, joins `B` to distance `r` is `<= C |B| e^{-kappa r}`.
  * This is section 7's crossing estimate for history polymers at every scale, with the per-scale normalisation (the
    named unchecked adaptation).
  * At fixed small-field `V_{j+1}` the scale-`j` part is the fixed-top-variable ratio of 3.2. Where `V_{j+1}` is large
    field, the rarity comes from the scale-`(j+1)` law. Chains of bad regions across scales are exactly what the
    history polymers count.
* **Consequence for (ii).** The composition is not "routine given (i), a union bound over scales". A disagreement can
  cross a scale-`j` bad region, then a scale-`(j+1)` one, and so on. The bound must sum over multi-scale chains, which
  is the history-crossing estimate above. It closes if that estimate holds, but it is part of the work.

### Anything missing?

* The fibre constraint: boxes must be unions of `L`-blocks, and the single-site specification is degenerate (above).
* "Good" defined for pairs of boundaries, and couplings modulo gauge (above).
* Non-finite-range specifications in the percolation argument: disagreement can jump gaps with exponentially small
  probability. Fine, but it must be in the theorem.
* **Z2 layer.** Agreed that it is standard: product reference for the lift signs, couplings
  `J_p >= beta(1 - O(eps^2))` on good boxes, weak couplings only on SO(3)-bad boxes. Two points to add:
  * the kernel also fixes `tau'_{j+1}`, so `tau'_j` ranges over the Stokes fibre (closed cochains with the given coarse
    sums), and the low-temperature expansion runs on that fibre;
  * the decoder constraint applies only at scale 0.
* **Finite-range decomposition (d).** Agreed: it could replace the block estimate for the Gaussian part, but the
  large-field part needs the same annealed rarity whatever the route.
* **Section 14's spectral form (S).** Agreed that it is equivalent in strength and not more provable from M1's tools.

### Findings, one line each (follow-up 3)

* **GAP:** Lemma UV-TV (i) cannot hold uniformly in `V_{j+1}`. It must be restated annealed, with coarse and fine bad
  regions in the failure event. Then (ii) needs a multi-scale crossing estimate for Balaban's history regions, which
  is not a routine union bound.
* **GAP:** the good/bad Theorem A cannot assume domination by an independent percolation (badness is inherited). Its
  hypothesis must be an annealed Peierls bound per coupled copy, with "good" defined for pairs of boundaries and the
  coupling taken modulo gauge.
* NIT: (b)'s sliding-sheet example does not give influence `~ |J|`. State the obstruction as "no control of the box law
  on large-field boundaries (possible multimodality)".
* NIT: the rate of (a) is about `1/l_B ~ m^{d+1}/(log log g^{-1})^{d+1}`, not `m/log log g^{-1}` (the far-side weight
  in `OneBoxSum`). Boxes must be unions of `L`-blocks.

## Follow-up 4 (UV-TV rebuilt, `UV-TV.md` 7-13), 2026-11-22

Read: `../m1-tools/UV-TV.md` 7-13 in full. Nothing was built or re-run; the commit id was not checked (no git).

### Verdict

Both Follow-up 3 GAPs are resolved at the level of statement and hypotheses. UV-TV (i) is now averaged, with
law-distributed coupled coarse states and the coarse bad set among the bad data. Theorem A_good's hypothesis is an
annealed Peierls bound per copy, with goodness defined for pairs. The long-link decomposition is sound. I see nothing
in H0-H4 that is unavailable in principle; H1 and H2 are the real work and correctly sit in section 12, which is not
started.

The proof sketch of Theorem A_good, however, is **not sound as written**. Step 3 derives the Dobrushin-Shlosman
inequality "in stationarity" with `d(x) <= 1` on bad sites. That cannot produce decay: a bad cluster and its good
collar can sustain disagreement indefinitely, and a stationary coupling may carry it, with no link to `D`. The
activation and first-passage logic of steps 4-5 is the right idea, but it must be derived from a coupling **started
from agreement**, not from stationarity. FIXABLE with a known construction (below), but load-bearing. No FATAL, no GAP.

### Status of the Follow-up 3 GAPs

* **GAP 1 (the statement of UV-TV (i)): resolved as a statement.**
  * Section 8 couples coarse pairs whose marginals are both the law, or both the law given a common `H`. (A) resamples
    the far coarse data; (B) uses fresh randomness on the mirror side.
  * `Bad_j(omega)` includes the coarse bad set. The tower's failure event is a multi-scale chain, not a union bound.
  * Its content (section 12) is open, as the note says.
  * NIT: (B) should be written as the hybrid of two copies that are conditionally independent given `F_l`, with
    randomness indexed by region. Then `Cov <= ||f|| ||g|| (P(H_A != Y_A) + P(H_thetaA != Y°_thetaA))`.
* **GAP 2 (the hypothesis of Theorem A): resolved.**
  * Independent-percolation domination is withdrawn.
  * H2 is an annealed Peierls bound per copy, used through the min-trick, so only marginal bounds are needed.
  * Goodness is a property of the pair (equal `omega`, both small field, no links), and H3 is required only for
    boundaries in the supports.
  * The gauge is handled by working in Balaban's block-axial gauge relative to the given coarse configuration, which
    is fully gauge-fixed once the coarse data are equal near `J`. The phrase "modulo gauge" in section 8 should say
    this.

### Theorem A_good: the proof sketch

**What is sound.**
* **Step 1, the mixture-first coupling.** Draw `(omega, omega')` from `Pi`, then couple `mu_omega` with
  `mu'_{omega'}`: correct marginals.
* **Step 3 on good boxes.** Changing boundary sites one at a time and gluing gives the multi-site coupling bound. The
  far-to-near coupling of 10.2 gives per-site disagreement bounds, so `k_J(z)` splits by site.
  * Nested maximal couplings for the tail families `{|y - z| >= r}` exist simultaneously (Goldstein's maximal coupling
    for a monotone family), so `E[#disagreements] <= Sum_r #(shell r) TV_r` is legitimate.
* **Step 5's averaging.** H2 for arbitrary finite unions of boxes gives the joint bound for all clusters of a chain at
  once; "factorises" is loose wording for that. The min-trick handles the two copies. The lattice-animal count and H4
  close the sum.

**What is not sound, and the fix.**
* **The problem.** Step 3, second bullet: "if `x` lies in a bad box ... `d(x) <= 1`", in a stationary coupling.
  * The resulting inequality `d <= min(1, M d + s)` has solutions with `d = 1` on bad clusters that are not connected
    to `D`. A disagreeing cluster `K` makes its collar disagree with weight `~ k |K|`, and the collar re-disagrees `K`
    with weight `|K|`. The loop gain `~ k |K|^2` is not small for large clusters.
  * Persistent disagreement inside an isolated bad cluster is compatible with a stationary coupled chain. The bad-box
    coupling is "arbitrary", and once the boundaries differ nothing forces agreement back.
  * So stationarity alone gives no decay in `dist(B, D)`. Bad clusters near `B` would contribute `~ eta`, independent
    of the distance.
* **The fix.** Make activation explicit, and work with the minimal solution.
  1. **Bad boxes far from `D` with `omega = omega'` near them:** H0's agreement clause makes the two specifications
     equal, so couple them **identically** whenever the boundaries agree. Then
     `Sum_{y in J} P(disagree after update) <= |J| P(some disagreement in the r_int-collar)`. That is the activation:
     influence `|J|` per collar site, not a spontaneous `d <= 1`.
  2. **Start the coupled dynamics from configurations that agree** outside `D` and outside the set where
     `omega != omega'` (possible, since `omega`-consistency is local per box). Iterate in time: `d_n` increases
     towards the **minimal** solution of the inequality, which is exactly the first-passage chain sum of step 5, with
     clusters activated once and capped at 1.
  3. **Pass to the limit** `n -> infinity` along a subsequence. The state space is compact, so couplings are tight. Each
     marginal converges to `mu_omega` by uniform ergodicity (Doeblin floor). The disagreement event at `x` is **open**,
     so `P(Y_x != Y'_x) <= liminf d_n(x)` (portmanteau).
  
  This replaces step 2's existence of a stationary coupling. It also removes the need for the Feller property, which
  fails anyway: optimal couplings are not continuous, and the hard characteristic functions `chi` are not Feller.
* **NIT on unique ergodicity.** The Doeblin floor gives a density lower bound for each box law. Ergodicity of the
  block heat bath on the `omega`-consistent set also needs block moves to connect it, and Balaban's per-cube
  conditions can straddle boxes. Either take boxes as unions of Balaban's `M R_j`-cubes as well as `L`-blocks, or add a
  short argument (create first, then remove). Qualitative only.

### The long-link decomposition (H0, 10.1)

* **Sound.**
  * `e^{E(X)} = e^{m_X}(1 + h_X)`, with `m_X` the infimum over the `omega`-support and `0 <= h_X <=
    e^{osc} - 1`, is a positive decomposition for real terms. A non-chosen link contributes the field-independent
    factor `e^{m_X}`, so a box with no chosen link has a specification of range `r_int`.
  * The link weight is bounded pointwise: `w(l ⊂ Lk) = ∫ Prod_l h_X Prod_{not l} (1 + h_X) ... / ∫ Prod_all (1 + h_X)
    ... <= Prod_l sup h_X`, jointly with any bad-box event. So H2's link part is immediate.
  * The far coarse data (`D`) enter only through chosen links and constants, as 10.1 says.
* **NIT on the size of the tails.** On small field, the localised pieces of the main term `A_j(U_j(V))`, through the
  background's decay [15] (190), are of size `~ p(g_j)^2 e^{-kappa d}`, not `O(1) e^{-kappa d}`. So `r_int >~ log p/kappa`.
  This is still inside `l_B ~ (log p/m)^{d+1}`.
* **Large-field regions.** Large-field regions use the local bare Wilson action inside `T`, not the background, so they
  create no long tails of size `g^{-2}`. Worth one sentence, since otherwise a reader worries about long-range
  couplings of order `g^{-2} e^{-kappa d}` from large fields.

### Is anything in H0-H4 unavailable in principle?

* **H0:** available (above).
* **H1** (pattern coupling with agreement off `D`-connected bad chains): available in principle. The pattern marginal
  is a positive contour gas with small activities and small many-body interactions, obtained by integrating the
  small-field fluctuations, and such gases are in the uniqueness regime (disagreement coupling or a cluster
  representation).
  * But this is genuine work: the interactions are not a hard core, and the gas also contains the domain history
    (functions of the field at all scales `<= j`) and unreleased regions from finer scales. It belongs to section 12,
    as stated.
* **H2:** available annealed. Pointwise in the coarse field it holds only where the coarse field is small field, and
  needs the pointwise fibre-normalisation lower bound (the named unchecked adaptation). The coarse part comes from the
  scale-`(j+1)` law, so it is part of the multi-scale crossing estimate. Nothing hidden.
* **H3:** available. The box law on a good box is a truncated, perturbed Gaussian. The hard small-field truncation at
  `~ p(g)` standard deviations changes total variation by `e^{-c p^2}`, and the Pinsker step holds uniformly over
  boundaries in the support. The rate `lambda ~ 1/l_B` is now right.
* **H4:** a smallness condition on `eta = e^{-c p0}`. Available.
* **Unimodality (11):** consistent and correctly scoped. It is claimed only given `omega`, on good boxes; the mixture
  carries the multimodality as indices. The Doeblin floor is correctly called qualitative.

### Findings, one line each (follow-up 4)

* No FATAL, no GAP. Both Follow-up 3 GAPs are resolved at the statement and hypothesis level. The content (H1, H2, the
  multi-scale crossing, section 12) is open, as stated.
* FIXABLE (load-bearing): Theorem A_good's step 3 "in stationarity, `d <= 1` on bad sites" cannot give decay, since
  isolated bad clusters can sustain disagreement. Rewrite it as: identical coupling on bad boxes with agreeing collar
  (H0), a coupled dynamics started from agreement, the minimal solution as the first-passage chain sum, and a weak
  limit with portmanteau. Drop the stationarity and Feller step.
* NITs: block-move irreducibility for unique ergodicity; the size of the long-link tails (`p^2 e^{-kappa d}`,
  `r_int >~ log p/kappa`); spell out (B) as a hybrid of two conditionally independent copies; say "block-axial gauge"
  instead of "modulo gauge".

## Follow-up 5 (static form, `UV-TV.md` 14-20), 2026-11-22

Read: `../m1-tools/UV-TV.md` 14-20 in full. Checked against the Lean layer's exact condition:
`Attempts.R3.GDSw block k e γ := ∀ x, Σ_{j : x ∉ block j} k j x * e j x ≤ γ * coverage block x` (a per-site column
condition), and `cov_le_weighted_on` / `theoremA_on` (`hcov : ∀ x, cmin ≤ coverage x`, `cmin ≥ 1`). Nothing was built
or re-run; the commit was not checked (no git).

### Verdict

* **The author is right about my Follow-up 4 fix. It does not close.** I claimed that the minimal solution of the
  capped inequality is a first-passage sum with clusters "activated once". It is not. With Hamming counting, a bad
  box and its collar have loop gain `>= 1`, so any positive input drives the minimal solution to 1 on the cluster.
* **The static repair is the right idea.** Composite boxes carry the cluster's whole conditional law, and Lemma C's
  marginal estimate replaces the box-by-box counting.
* **Lemma C is correct in principle**, for the fibre-constrained, gauge-fixed, truncated and perturbed measure, with
  one omission: long links.
* **The Dobrushin-Shlosman bookkeeping with variable blocks is wrong as written**, in three ways:
  * the multiplicity rule breaks the per-site condition at sites outside large composite boxes;
  * sites in gaps narrower than `l_B` are left uncovered;
  * the merging cascade (`w` growing like `log |K|`, merging within `2w`) makes composite boxes percolate in large
    volumes, so the per-pattern condition fails on the whole torus and volume uniformity is lost.
  
  All three are repairable: constant multiplicity, merging at scale `l_B`, and localisation with truncated cluster
  sizes.
* **The per-pattern-pair then average structure is valid as a reduction.** The within-pattern covariance needs no H1,
  but the comparison of two measures in (A) and the pattern-index covariance in (B) are conditional on H1, which is
  open.
* No FATAL; one GAP (the cascade and volume uniformity); several FIXABLE points.

### (1) Is section 15's argument against the dynamic fix right?

**Yes, and it overturns my Follow-up 4 proposal.**
* With identical coupling only when a bad box's collar agrees, and arbitrary coupling otherwise, a box `J` that
  disagrees makes its adjacent collar sites disagree with probability `~ 1`. A value change of size `O(1)` against
  width `g` gives total variation `~ 1`, so `k(y, z) >~ 1` for adjacent `y, z`. The collar in turn re-infects `J` with
  weight `|J|`.
* So the capped system `d_K <= min(1, |K| Sum_{coll} d)`, `d_coll >= k d_K + s` has minimal solution 1 on `K` for any
  input `s > 0`, as soon as `|K| k >= 1`. Already one box suffices.
* Activation is therefore not proportional to the instantaneous input: it accumulates over time. My "first passage,
  activated once" bound was wrong, and I withdraw it.
* **What exactly is obstructed:** Hamming bookkeeping of bad boxes, box by box. It discards how large the
  disagreement is that reaches a bad box. Dynamics as such is not obstructed. A block heat bath in which each
  composite box is resampled as one block, with Lemma C's coupling, does not saturate:
  * the cluster interior lies at distance `w > r_int` from outside sites, so it has no direct influence outside
    (finite range);
  * the whole composite box is resampled at each update, so earlier inside disagreement is forgotten.
  
  The static and dynamic forms are then equivalent; the composite box is what matters.

### (2) Lemma C

**Correct in principle.** Given `omega`, the law of `W` given `sigma` is `w(c) Z(c, sigma)/norm`, where `c` lives on
`K` plus the inner collar layer (finite range, H0). The total variation of the `c`-marginal is controlled by the
oscillation in `c` of `log Z(c, sigma) - log Z(c, sigma')`, the mixed variation. The checks:
* **Gaussian part.** On `ker Q` (the fibre constraint, internal to `L`-blocks; the collar is a union of boxes, hence of
  blocks), the collar is a massive Gaussian (Poincare). `log Z` is a quadratic form in the Dirichlet data, and the
  cross term is the bilinear form `Delta c^T G_{in,out} Delta sigma / g^2`, with `|G_{in,out}| <~ e^{-m d}`. Right.
* **Analytic perturbation.** Its contribution to `log Z(c, sigma)` that depends on both `c` and `sigma` comes from
  connected clusters spanning the collar: decay `e^{-kappa' w}`.
  * Data differences `|Delta c|, |Delta sigma| <~ 2 L eps_j` lie inside Balaban's analyticity radius (that is how
    `eps` and `alpha` are chosen), so Cauchy estimates give the stated form.
  * Use `min(m, kappa')` as the rate in `w`.
* **Hard truncation `chi`.** Its mixed variation also needs a correlation across the collar, so it is
  `<~ e^{-c p^2} e^{-m' w}`. It is not a free additive `e^{-c p^2}`, which for large `|K|` could exceed the target
  `1/|K|`. Write it this way.
* **Gauge.** Block-axial gauge relative to the coarse field. The collar's coarse field is not coarse-bad (coarse-bad
  boxes are in `Bad`, hence in `K`), so inner and outer data are within `C L eps` of the same background. Fine.
* **"The outer boundary reaches the cluster only through the collar"** holds by finite range given `omega`, **except
  through chosen long links.** Bad boxes are defined without link endpoints (section 8: large-field domains,
  unreleased regions, labels, Z2 excitations, the coarse bad set), and composite boxes are components of
  `Bad(omega) ∪ Bad(omega')`. A link from `K` to a box beyond the collar joins `K`'s law to far `sigma` directly.
  * **Fix (FIXABLE):** take components in the graph that also has the chosen links as edges. Link-joined clusters form
    one composite box, possibly non-contiguous.
  * Each link is then paid by `e^{-kappa s}` in the averaging, against the `lambda s` it saves in `dist_omega`. That
    is fine, since `lambda << kappa`.
* **The `w` arithmetic.** With `w = (2/m) log(C |K| p)`, `e^{-m w} = (C |K| p)^{-2}`. Then the claimed
  `C |W|^2 p^2 e^{-m w} <= |W|^{-1}` does not follow: one gets `~ (|W|/|K|)^2/C^2`, and `|W|/|K|` grows with `w`.
  Something like `w = (3/m) log(|K| p) + C` is needed, or whatever the per-site condition below requires. Any
  logarithmic `w` works, which matters for (3).

### (3) Dobrushin-Shlosman with variable blocks and multiplicities; merging

`GDSw` is a **per-site column** condition: for each site `x`, the influence of `x` on all blocks not containing it,
weighted, is at most `γ` times the number of blocks containing `x`. The one-box row sum is equivalent to it only for
translates of one box (`sum_box`). For variable blocks the columns must be checked.
* **(a) The multiplicity must be constant, not proportional to `|∂W|`. FIXABLE.**
  * Each copy of `W` is a separate block. So it adds `k_W(x) e^{lambda E}` to the column of **every outside site `x`**
    near `W`.
  * With `n_W ~ |∂W| (log p)^{d+1}/gamma`, the column at a site just outside a large `W` is `>~ |∂W| (log p)^{2d+1}`,
    against `gamma * coverage(x) <= gamma l_B^d`. It fails for large `W`.
  * What the inside needs is small. Sites of `W` deeper than `r_int` have **zero** influence outside (finite range),
    and sites in the outer `r_int`-layer influence adjacent good boxes with column `~ l_B^{d-1} (log p/m)^{d+1}`.
  * So take `n_W := ceil(C l_B^{d-1} (log p/m)^{d+1}/gamma)`, the same for all `W`. The outside columns then need
    `n_W (log p/m)^d <~ gamma c l_B^d`, that is `l_B >~ (log p/m)^{2d+1}/gamma^2`. This is a harmless enlargement of
    the boxes.
* **(b) Coverage of gaps. FIXABLE.**
  * The family keeps only good boxes that meet no composite box. A site in a gap or concave pocket narrower than `l_B`
    (between two composite boxes at distance between `2w` and `l_B`, or inside an irregular `W`) lies in no block.
  * Then `coverage(x) = 0`, which violates `hcov` (`cmin >= 1`) and the column condition.
  * Merge composite boxes closer than `l_B + 2 r_int`, and round each `W` up to a union of grid boxes with pockets
    filled. The entropy changes from `G = 2w` to `G ~ l_B`: `(C l_B^d)^n` against `eta^{n/2}`, with
    `l_B^d = polylog(p)` far below `e^{c p0}`. Fine.
* **(c) The merging cascade: not volume-uniform as written. GAP (fixable-looking).**
  * With `w(K)` growing like `log |K|` and merging within `2w`, a cluster of size `n` reaches out to distance
    `~ (2/m) log(n p)`.
  * Bad boxes have density `~ eta`, so typical spacing `eta^{-1/d}`. Once `(2/m) log(n p) > C eta^{-1/d}`, that is
    `n > n* ~ exp(c m eta^{-1/d})`, the cluster absorbs every bad box within reach, grows, and reaches further. It
    percolates through the volume.
  * A seed of size `n*` occurs somewhere once the volume is `>~ eta^{-c n*}` (doubly exponential in `eta^{-1/d}`).
    On such tori one composite box spans everything, and the per-pattern condition, being global, gives nothing.
    Since M1 claims uniformity in the volume, this must be fixed. Two pieces:
    * **Localise** Theorem A_good to a region `Λ'` around `B ∪ D` of size `~ (dist + R)`, as the conditional measure
      given the outside. The outside enters as a boundary condition at distance `>~ t`; its influence is covered by
      the same estimate.
    * **Truncate** cluster sizes: patterns with a cluster in `Λ'` above `n_max := C log(#boxes in Λ')/log(1/eta)` go
      into the failure event, with probability `<= #boxes * eta^{c n_max}`.
  * Then `w <= w_max ~ (3/m) log(n_max p)` and no cascade occurs. It must be checked that `#boxes in Λ'` stays below
    the cascade threshold at every scale.
    * At fine scales, `#boxes ~ (R/(L^j a))^d` grows as `a -> 0`, while `eta_j = e^{-c p0(g_j)}` with
      `p0 = A0 (log g_j^{-2})^p`. The threshold beats `(R/l_j)^d` when `p >= 2`, or when `p = 1` and `c A0/d > 1`:
      Balaban's constants, to be stated.
    * Near `L_*`, `#boxes` is bounded.
* **(d) Off-support extension. FIXABLE.**
  * "The specification extended off the support (only used `mu`-a.s.)" is not enough for the oscillation iteration
    behind `theoremA_on`. It bounds `sup_{sigma, s} |h(sigma) - h(sigma^{z -> s})|` through single-site hybrids, and
    the `omega`-supports are not product sets: small-field and large-field constraints are per plaquette or per cube.
  * Inside composite boxes, hybrids of two admissible large-field configurations can leave the support, where no
    influence bound holds.
  * Use the **coupling (Hamming-Wasserstein) form** of Dobrushin-Shlosman instead. It needs couplings of block laws
    only at pairs of in-support boundaries, which is what H3 and Lemma C give. Iterate it by the block heat bath with
    composite boxes as blocks (no saturation, see (1)), or as a fixed point of couplings. The Lean layer needs a
    support-relative or coupling version; that is new, but routine.
* **(e) The averaging (ii).** Composite boxes now contain gaps up to `~ l_B`, so covering half a path of length `R`
  needs only `~ R/(l_B + w_max)` bad boxes. The averaged term is `<~ (C l_B^d eta^{1/2})^{R/(l_B + w_max)}`: still
  exponential, with a rate reduced by `l_B + w_max`. Fine after (c).

### (4) Per pattern pair, then average, with H1 open

* **Valid as a reduction.**
  * For one measure, `Cov_mu(f, g) = E_w[Cov_{mu_omega}(f, g)] + Cov_w(mu_omega f, mu_omega g)`. The first term needs
    only the per-`omega` Dobrushin-Shlosman form (single measure, no pattern pair) and the Peierls average: no H1.
  * The second term, the pattern-index covariance, needs two things:
    * that `mu_omega f` depends on `omega` only near `supp f`, which is the two-measure comparison with
      `omega != omega'` far away (composite boxes there act as source);
    * that the pattern law itself decorrelates, which is H1.
  * (A) needs H1 for the coupling `Pi`.
* **Not circular in principle.** H1 is a uniqueness or decorrelation statement for the positive marginal law of the
  discrete data. Its effective interactions come from Balaban's convergent small-field expansions (exponentially
  decaying, small), not from the statement being proved. So H1 is a separate input, not hidden in the conclusion.
* **But it is real work** (many-body, non-hard-core interactions; the domain history as a function of the field). So
  the result is, as the note says, conditional on H1 and on section 12.

### Sections 17-19, briefly

* **17 (quenched H2):** correct framing. Pointwise only outside the coarse bad set, with the pointwise fibre
  normalisation as the named unchecked adaptation.
* **18 (coarse bad set):** the sharp threshold `2 eps_{j+1}`, outside the support of Balaban's smooth small-field
  functions, puts coarse-bad boxes in a large-field domain of every term. Clean. "No joint mixture across scales" is
  right.
* **19:** the interpolation (Pinsker) step is fine. Truncation contributes `e^{-c p^2}` additively here, which is
  harmless for a single box, unlike Lemma C's large clusters (see (2)). The values of `r_int`, (B) and the gauge are
  fine.

### Findings, one line each (follow-up 5)

* No FATAL.
* **Concession:** my Follow-up 4 dynamic fix was wrong. Section 15 is right that Hamming bookkeeping of bad boxes
  saturates. The obstruction is to box-by-box counting, not to dynamics with composite boxes as blocks.
* **GAP:** the merging cascade (`w ~ log |K|`, merging within `2w`) makes composite boxes percolate in volumes beyond
  `~ eta^{-c exp(c' eta^{-1/d})}`, so the global per-pattern condition fails. Localise to a region around `B ∪ D`,
  truncate cluster sizes at `n_max ~ log(#boxes)/log(1/eta)`, and check the threshold against the box count at every
  scale (needs Balaban's `p >= 2` or `A0` large).
* FIXABLE: the multiplicity must be a constant `~ l_B^{d-1} (log p)^{d+1}/gamma`, not proportional to `|∂W|` (which
  breaks the column condition outside large `W`). Then `l_B >~ (log p)^{2d+1}/gamma^2`.
* FIXABLE: gaps and pockets narrower than `l_B` are uncovered (`coverage = 0`). Merge and round composite boxes at
  scale `l_B`.
* FIXABLE: Lemma C must include chosen long links as edges of the cluster graph. Fix the `w` arithmetic (about
  `(3/m) log(|K| p)`, with rate `min(m, kappa')`). The truncation cross term is `e^{-c p^2} e^{-m' w}`.
* FIXABLE: the oscillation iteration needs hybrids, which leave the non-product `omega`-supports. Use the coupling form
  of Dobrushin-Shlosman (a support-relative Lean layer).
* Open, as stated: H1, on which (A) and (B)'s pattern-index covariance depend; and section 12.
