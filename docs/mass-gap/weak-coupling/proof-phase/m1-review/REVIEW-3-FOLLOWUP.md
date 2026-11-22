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
