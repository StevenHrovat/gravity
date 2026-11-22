# Response to REVIEW-3 and the REVIEW-2 follow-up (m1-tools, 2026-11-22)

Brief (coordinator): `../m1-review/REVIEW-3.md` and `../m1-review/REVIEW-2-FOLLOWUP.md` agree that the verdict
"complete at paper level" overstates what is written. Order: N-1, H5 and H6 first, then H1, H2, H4, N-2, H3. Report
after H1 and H2. Stop at anything fatal or much harder than marked. Correct the verdict in `M1-PLAN.md` 0 to what is
written. Claim marks as in `NOTE.md`.

Part 1 (sections 0-6) covers N-1, H5, H6, H1 and H2. Part 2 (sections 7-10) covers H4, N-2, H3, H7 and H8.

**Part 2 in brief.**
* **H4 (paper, citation-level inputs):** R10 redone on the non-negative terms of Balaban's (1.104). The A-cluster
  mixture replaces the "event" `E_D`. The top variables' normalisation at scale `K` is paid from the large-field
  budget, as in Balaban's next step. Rate `c κ/(M L_*)`.
* **N-2 (paper sketch):** the block-observable class is dense in the **OS norm**, by conditional decorrelation at
  scale `ℓ`, whatever the vortex action `c0`. Sub-block vortices erased by M1 drop out of reflected pairings. `L²`
  density, which would need `c0 b > 1`, is not required.
* **H3 (paper on citation-level inputs):** `S1-INDUCTION.md` gives:
  * the order of constants;
  * `Form_k` with the window form;
  * the step in eleven operations;
  * the new E-row 7c: coarse plaquettes meeting holes, paid by the deep set's action, `r0²/(8 g_k²) ≥ C(C_1) p²`.
* **Labels (section 11, after the part-1 follow-ups and the owner's reading):** R8 is restored for labels.
  * A small released label is `a_ℓ e^{L_ℓ}`, with `L_ℓ` small, local, gauge invariant and without linear coupling.
  * Its field dependence is a dimension-4 point term, which shrinks by `L^{−4}` per step. So the carrying cost is
    summable, uniformly in the label's lifetime.
  * The remainders stay with the label (constant into `a_ℓ`), not with the coupling, so [I]'s running is untouched.
  * **Paper** on citation-level adaptations; components above Balaban's `ε_*` are **sketch**.
* **Nothing fatal.** The remaining sketch points are listed in `M1-PLAN.md` 0.

## 0. Result in plain words

| finding | agree? | outcome |
|---|---|---|
| N-1 small field at scale 0 | **yes** | fixed: at scale 0, small field means SU(2)-regular, so `τ = +1`; from scale 1 on, SO(3)-regular. Every bare flip lies in Balaban's scale-0 large-field set and is charged its action (the owner's reading: below the quantum a thin sheet is a cost, not a particle). Section 1. |
| H5 twist-free test | **yes**, on all five points | restated: the test loops have length up to `λ = 8(ℓ_max + 2)`, not 8; the cap is `ℓ_max ≥ C L + 1`; the filling is the implicit-function critical point, not "the minimiser"; owned bonds lie outside the Dirichlet data; the Z2 bullet is corrected. **Paper**, except "cap reached implies irregular `W`" (**sketch**, tied to `FILL.md` 0.2). Section 2. |
| H6 `f(P) ≤ |P|/6` | **yes**, both counterexamples are right | the claim is withdrawn. The per-flip factor `poly(β)` stays at **citation** level: a rank count gives the exponent `β^{3/2}` per removed plaquette, and Balaban's partition-function bounds give the ratio. Section 3. |
| H1 labels as `a_ℓ (1 + h_ℓ)` | **yes**: asserted, not derived | **repaired by a different form, which needs no smallness of `h`.** A label is extracted at the release of its component, as a positive fixed-domain factor `Φ_ℓ(X; V)`. Balaban's (1.73)-(1.75), applied with `F = 1_ℓ`, give its relative stability in the complex directions. This is all the later steps use, as for his fixed domains in (1.103). Large labelled components are carried until their image is small. **Paper** for components with `δ_k |X| ≤ 1/4`. Within Balaban's lifetime it is **citation-level**. The super-rare tail beyond the lifetime is **sketch**, the same item as R2's footprint-weighted lifetime. Section 4. |
| H2 decoder components | **yes** | **repaired by a local decoder.** Decode separately in each connected union of Balaban's `M R_0`-cubes containing a bare flip. This is local, measurable and inside Balaban's scale-0 large-field domain (by N-1), so it enters his `T`-operations as a function of their own variables. **Paper.** Section 5. |

**Neither H1 nor H2 is fatal.** H1 was the one at risk of being much harder than marked. With the factor kept
unexponentiated, it needs no new decoupling estimate. One point should be checked against Balaban's text: whether his
first-order bound before (1.73) is per `M R_k`-cube or per component (section 4.4).

**One exact observation is used throughout** (section 1.1): given the bare SO(3) field, the Z2 layer is a Z2 lattice
gauge theory with couplings `J_p = (β/2)|tr U_p|`. Conditioning on a label inverts the SO(3) action on the label's
plaquettes. This is the reason for N-1, and it fixes the label's bare weight exactly.

## 1. N-1: the small-field rule at scale 0

### 1.1 The Z2 layer given the SO(3) field (exact)

* Choose a measurable lift `Û_b` of each SO(3) bond `V_b`, so that `U_b = s_b Û_b` with `s_b = ±1`. Haar measure on
  SU(2) is Haar measure on SO(3) times the uniform measure on `s`.
* Then `tr U_p = (ds)_p tr Û_p`. Writing `τ̂_p = sign tr Û_p`, the Wilson weight is
  `exp((β/2) Σ_p τ_p |tr U_p|)` with `τ_p = (ds)_p τ̂_p`. Here `|tr U_p| = 2|cos(φ_p/2)|` depends on `V` only, where
  `φ_p` is the SO(3) plaquette angle.
* **So, given the bare SO(3) field `V_0`, `τ` is a Z2 lattice gauge theory** with plaquette couplings
  `J_p(V_0) = (β/2)|tr U_p| ∈ [0, β]` and background twist `τ̂(V_0)`; `dτ = dτ̂` (monopoles) depends on `V_0` only.
* **Centre multiplication.** For a bond set `B`, the map `U ↦ (−1)^{1_B} U` preserves Haar measure and `V_0` exactly,
  flips `τ` on `S = d1_B`, and changes the action by `β Σ_{p ∈ S} tr U_p`.

**Consequence.** Given `V_0`, the weight of flips on a closed set `S` relative to none is
`exp(−β Σ_{p ∈ S} |tr U_p(V_0)|)`. As a function of `V_0` it is `e^{−2β|S|}` times `exp(+β Σ_{p ∈ S} (2 − |tr U_p|))`:
the factor contributes `+βφ_p²/4` per plaquette, so the net SO(3) term on `S` is **inverted**, `+βφ_p²/8` instead
of `−βφ_p²/8`. A bond all of whose
plaquettes lie in `S` then has no restoring force. So the SO(3) field near a label is not a small field at the bare
scale. This is REVIEW-2 follow-up N-1 in exact form, and it is why the τ-blind rule fails at scale 0.

### 1.2 The rule

* **Scale 0:** small field means SU(2)-regular, `|U_p − 1| ≤ ε_0` (Balaban's bare condition). This implies `τ_p = +1`.
* **Scales `k ≥ 1`:** small field means SO(3)-regular ((2.17) with the SO(3) distance). The coarse layer `τ'_k` enters
  only through label factors (section 4).
* **Consequences:**
  * every bare flip `τ_p = −1` has `|U_p − 1| ≥ √2`, so its `M`-cube lies in Balaban's scale-0 large-field set `P_0` in
    **every** term of his decomposition of unity (the small-field characteristic function vanishes there);
  * a flip's own Wilson action is `≥ β` (`1 − ½ tr U_p ≥ 1`). A part `p0²` of it pays the scale-0 large-field
    factor; the rest, `(1 − δ)β` with `δ = p0²/β`, stays for the label count, which then uses `16 b(1 − δ)`
    (REVIEW-3 H7.4).
* **The owner's reading** (`../../PREP.md`, "N-1 and the glueball"): a thin closed sheet at the lattice scale is far
  below the quantum. It cannot exist as a glueball, so it is charged its action. That is exactly this rule.

**Where it changes text:** `S1-CURRENT.md` (F-c); the R9 row of `CLOSE-OUT.md` 5 and of `M1-PLAN.md` 0; main-line
item 3 of `M1-PLAN.md` 0 ("the Z2 background is `+1` in small-field regions" is now true at scale 0 by definition and
irrelevant above it). **Status: paper.**

## 2. H5: the twist-free test, the cap, and the filling

1. **The test (restated).**
   * Let `H` be the current hole and `O(H)` the bonds at distance 1 from `H` that are not in it.
   * `H` is **twist-free** if every closed loop `γ` in `O(H)` with `|γ| ≤ λ := 8(ℓ_max + 2)` satisfies
     `|Hol(γ) − 1| ≤ C_tw r0 |γ|²`.
   * Plaquettes avoiding `H ⊇ H_0` have angle `< r0`, so loops that bound inside `O(H)` pass automatically. The test
     bites on loops that **link** the deep structure.
   * **Not vacuous:** the `3 × 3` loop around a deep plaquette has length 12, the transverse loop around a slab of
     thickness `w` has length `4(w + 3) ≤ λ` for `w ≤ 2ℓ_max + 1`, and both are included.
   * The growth stays deterministic: layers are added while the test fails, at most `ℓ_max` of them, and components that
     touch are merged.
2. **The cap.**
   * `ℓ_max := C_1 L` with `C_1 L ≥ C L + 1`. A localised core (gauge representative in a ball of radius `ρ ≤ C L`) then
     bounds inside `H` after `ρ + 1` layers, so no linking loop is left: it always finishes.
   * Thin centre sheets finish after `O(1)` layers, because `Ad(−1) = 1` (`REVIEW2-RESPONSE.md` 3).
   * **If the cap is reached:** some loop `γ` (`|γ| ≤ λ`) links a deep structure that does not bound within distance
     `ℓ_max ≥ C L` of `H_0`, with SO(3) twist `θ > C_tw r0 |γ|² ≥ 144 C_tw r0 ≥ 4 ε_{k+1}` (a linking loop has `|γ| ≥ 12`; corrected after the REVIEW-3 follow-up). By `FILL.md` 0.2, the averaged coarse loops
     around its pierce point enclose fractions summing to 1, so some coarse plaquette has angle `≳ θ/4 > ε_{k+1}`, and
     `W` is irregular.
   * **Status of "cap reached implies irregular `W`":** **sketch**. The nonabelian "fractions sum to 1" step of
     `FILL.md` 0.2 is the sketch-level piece, now tied to this rule.
3. **The filling** is defined as the critical point given by the implicit function theorem: the unique critical point
   of the Wilson action on the plaquettes meeting `H`, within sup-norm distance `c/diam²` (slabs: `c w^{-2}` patchwise)
   of the axial-gauge extension of the data. It is deterministic, measurable and analytic in the data. "Least-action
   configuration" is withdrawn.
4. **Owned bonds** for E7.J near a hole are chosen outside the Dirichlet data `O(H)`. Next to a thin slab such bonds
   exist on every block face, because the slab is thinner than a block.
5. **Correction** to `REVIEW2-RESPONSE.md` 3, "The Z2 part". The SO(3)-deep sheets of G6 are thick at the bare scale
   (`τ = +1` along them). A bare-thin sheet (`τ = −1`) is SO(3)-flat, never excised, and under N-1 a scale-0 large
   field whose closed part becomes a label.

**Kept:** the slab gap `≥ 2(π/(w + 1))²` is independent of the area (REVIEW-3), and the data bound `C r0 w ≤ C c L^{-3}` is
small against it. **Status: paper**, except item 2's last step (**sketch**).

## 3. H6: the per-flip normalisation

* **Withdrawn:** `f(P) ≤ |P|/6`, and the claim that the Jensen route of `CLOSE-OUT.md` 4 works for arbitrary `P`.
  The reviewer's two counterexamples (the timelike slab with `f = |P|/3`; the 20 plaquettes around a plaquette's bonds
  with `f = 0` and 9 free directions) are correct.
* **Restated claim (R7′):** `P(τ_p = −1 for all p ∈ P) ≤ e^{−β|P|} Z_{−P}/Z` and `Z_{−P}/Z ≤ (C β^{3/2})^{|P|}`.
* **Exponent (paper):** in the Gaussian approximation `Z_{−P}/Z` counts freed directions. Removing one plaquette removes
  one 3-row block from the coboundary matrix, so the rank of the quadratic form modulo gauge drops by at most 3. Each
  freed direction gains at most `C β^{1/2}`, with compact Haar range.
* **Ratio (citation):** Balaban's two-sided bounds for locally modified actions ([16] Theorem 1 and its proof; [V]
  p. 380 in `d = 4`), with the region of the removed plaquettes treated as a large-field region (Haar integral `≤ 1`
  above, Gaussian lower bound below). This is the R7 citation, now with the right exponent.
* **What uses it:** the decoder's Peierls sum (`REVIEW2-RESPONSE.md` 1; now only a probability statement, section 5) and
  the label count. Both need only `poly(β) e^{−β}` per flip, which the margins absorb. **Status: citation**, with the
  exponent derived.

## 4. H1: labels as fixed-domain factors

**Corrected in section 11** (after both part-1 follow-ups): the carrying of 4.4 undercounted the per-step cost and
leaned on (1.103) beyond one step. 4.3's "real backgrounds are never compared" is wrong. Section 11 restores R8 for
labels.

### 4.1 What was wrong, and what is actually needed

* `WRITEOUTS.md` 1 asserted `F_ℓ = a_ℓ (1 + h_ℓ)` with a constant `a_ℓ` and a small `h_ℓ`. That needs a two-sided bound
  across **real** backgrounds, which Balaban does not give (REVIEW-3 H1, follow-up G2).
* **But nothing later needs `a_ℓ` constant or `h_ℓ` small.** It needs three properties of the label's weight `Φ_ℓ`,
  as a function of the current field on a fixed domain:
  * **(P1)** positive on real configurations;
  * **(P2)** relatively stable in the complex directions;
  * **(P3)** an upper bound for the count.
* These are what Balaban himself uses for his fixed-domain factors `T'_k(Y_i) 1` in (1.103)-(1.104).

### 4.2 Construction

* **Before release (the window form, for H3.2).** Each label pattern `ℓ` is a function of the bare `τ` on a decoder
  component, which lies inside a scale-0 large-field component (sections 1.2, 5). While that region is carried, the
  label is the indicator `1_ℓ` inside the region's `T`-operation. `T(Z) = Σ_ℓ T^ℓ(Z)`, each `T^ℓ` a positive operation.
* **At release** (Balaban's R-operation, [V] (1.70)-(1.72)), split each first-class component `X` by label pattern,
  before the Mayer expansion: `T_k(X) = Σ_ℓ T^ℓ_k(X)`. For `ℓ ≠ 0` write
  `T^ℓ_k(X) = Φ_ℓ(X; V) · T̂^ℓ_k(X)` with `Φ_ℓ(X; V) := T^ℓ_k(X) 1` and `T̂^ℓ_k` normalised (`T̂ 1 = 1`), positive.
* **The Mayer expansion** of the curly bracket in (1.72), with `T̂^ℓ` on the labelled components, is exactly Balaban's
  expansion for normalised operations on fixed domains, the one he writes for (1.103):
  * activities as in (1.92) without the first two sums, with a factor `e^{3δ}` per fixed domain;
  * convergence "without tree decay factors for the fixed domains, because there are no summations over them" ([V]
    p. 391).
  
  The polymers meeting a labelled domain become boundary terms attached to it. The unlabelled components are
  Balaban's. **Citation**, with the adaptation stated.
* **Result:** for a fixed family `𝓛` of labelled components,
  `ρ = Π_{X ∈ 𝓛} Φ_{ℓ_X}(X; V) · [Balaban's form, with the labelled domains as fixed domains]`.
  `ρ(V, τ')` is the sum of this over `𝓛 ~ τ'`.

### 4.3 The three properties

* **(P1)** `Φ_ℓ(X; V) > 0` for real `V`: a positive integrand times an indicator of an event of positive measure.
* **(P2)** In Balaban's variables `(U, J)` (real regular `U`, complex `J`), the integrand of `T_k(X, (U, J))` is that of
  `T_k(X, (U, 0))` times `e^{Δ}`, with `Δ` the small first-order term ([V] p. 379). His derivation of (1.73)-(1.75),
  with `F = 1_ℓ ≥ 0`, gives
  `|T^ℓ(X,(U,J)) 1 − T^ℓ(X,(U,0)) 1| ≤ (e^{sup|Δ|} − 1) T^ℓ(X,(U,0)) 1`.
  So `Φ_ℓ(U, J) = Φ_ℓ(U, 0)(1 + η)` with `|η| ≤ e^{sup|Δ|} − 1`. Real backgrounds are never compared: each fibre is
  compared with its own real base point.
* **(P3)**
  `sup Φ_ℓ ≤ (C β^{3/2} e^{−(1−δ)β})^{f(ℓ)} · e^{−2(1+β')p0(g_k)} e^{−κ d_k(X)}`
  (`f(ℓ)` = number of bare flips, at least 4 per labelled interior skeleton bond; R7′; [V] (1.89) improved by `d_k(X)`).
  This gives the count `e^{−16(1−δ)/g_k²} L^{(1−16b(1−δ))k}` per coarse bond. At coarse vertices the bound is per
  component (REVIEW-3 H7.1).

### 4.4 Carrying a label factor through later steps

**Small components, `δ_k |X|_k ≤ 1/4`.**
* Here `δ_k` is Balaban's first-order bound quoted before (1.73), `O(1) B^{3/2} A^{1/2} C_0 M^d R_k^{d+2} p²(g_k)
  q0(g_k) g_k`, which tends to 0 with `g_k`. I read it as a bound per `M R_k`-cube (the volume factor `M^d R_k^d`). If it
  bounds the whole component, the case split below is unnecessary.
* At the next step, `V_k = U_bg(V_{k+1}) e^{i g B}` with the fluctuation `B` in Balaban's domain. By (P2),
  `Φ_ℓ(V_k) = Φ_ℓ(U_bg)(1 + η(B))` with `|η| ≤ e^{1/4} − 1 < ½`.
* `(1 + η)` enters the fluctuation expansion as a fixed-domain polymer with a bounded activity, converging as in the
  (1.103) remark.
* The new factor is `Φ'_ℓ = Φ_ℓ ∘ U_bg` times the exponential of the clusters meeting the domain. It again has (P1)-(P3):
  * `U_bg` is analytic and maps complex fibres into complex fibres;
  * the attached clusters are bounded by `C(δ_{k+1} + c1)|X_{k+1}|`.
* **No growth that matters:** over all later steps the factor changes by at most
  `exp(C Σ_{k'} (δ_{k'} + c1)|X_{k'}|) ≤ exp(C|X| + C' √K polylog)`, since `|X_{k'}|` shrinks by `L^{-4}` per step and
  `δ_{k'} ~ g_{k'} polylog`. This is sub-exponential in `K`, so the count `L^{(1−16b')k}` is unaffected.
* **The real oscillation of `Φ_ℓ` is never bounded, and never needed.** Neither is R8's dimension-4 argument for
  labels: the labels are not E- or R-terms.

**Large components, `δ_k |X|_k > 1/4`.**
* Such a component is carried further as a Balaban large-field region (not released yet), until its image satisfies
  `δ |X_{k+n}| ≤ 1/4`; then it is treated as above.
* The extra time is `n ≈ ¼ log_L(4 δ |X|)` steps. The footprint shrinks geometrically throughout, so the extra entropy
  is `≤ C (log g^{-2}) Σ_n |X_{k+n}| ≤ 2C (log g^{-2}) |X|`, paid by the region's own large-field factors
  (`≥ c p0²` per cube) because `p0² ≫ log g^{-2}`.
* For `n ≤ R_k`, that is `|X| ≤ L^{4R_k}/(4δ)`, this at most doubles Balaban's lifetime in (1.80)-(1.81), and is
  absorbed in his constants (**citation-level**).
* Beyond that, the weight is `≤ e^{−c p0² L^{4 R_k}/δ}` and the extension needs the footprint-weighted lifetime
  (**sketch**, the same item as R2's, `M1-PLAN.md` 0).

### 4.5 Status

* **Paper** for the form and for small components.
* **Citation-level** for the Mayer expansion with normalised labelled operations, and for the extension within the
  lifetime.
* **Sketch** for the super-rare tail.
* **To check against the text:** whether `δ_k` is per cube (section 4.4).

**What this replaces:**
* `WRITEOUTS.md` 1, steps 2-4, are superseded;
* `S1-CURRENT.md` (F-f) becomes: "for each labelled released component `X`, a positive fixed-domain factor
  `Φ_ℓ(X; V)` with (P1)-(P3); before release, an indicator inside `T`";
* the parity sum of step 4 is an upper bound, not a closed form (labelled domains have a hard core, H7.3).

## 5. H2: a local decoder

* **The problem** (REVIEW-3 H2, follow-up G3 residual): with the global decoder, the event "the conflict component of
  `q` is `U`" depends on `τ` outside `U`. It is not a product of local factors, so it does not enter Balaban's
  `T`-operations, which factorise over components of his large-field domain.
* **Repair: change the blocking** (exactness holds for any measurable blocking, `Exact.lean`).
  * Let `D_0` be the union of the `M R_0`-cubes of Balaban's scale-0 grid that contain a bare flip. This is
    deterministic, a product of per-cube indicators.
  * In each connected component `C` of `D_0`, take the maximum-weight packing of positive-gain closed connected
    plaquette sets **contained in `C`**, with the tie-break absorb-on-tie, then smaller `|σ|`, then lexicographic in a
    fixed plaquette order (REVIEW-3 H8).
  * The output `τ'_0` is the sum of the chosen sets: closed.
* **Properties.**
  * **Local:** the output on `C` is a function of `τ` on `C`. By N-1, every flip cube lies in `P_0` in every term,
    so `C` lies inside one component of Balaban's `Z_0`. The decoder is therefore a function of the integration
    variables of that component's `T`-operation.
  * **Measurable and deterministic:** a finite maximisation per component.
  * **Label count unchanged:** each chosen set has positive gain, so more than half of it is flipped, at least 4 flips
    for the minimal one.
  * **Acts absorbed:** a lone flip is not closed, so it is not chosen.
  * **Covariance:** that of Balaban's grid (his domains use the same `M R_j`-cube grids), with a fixed tie-break on
    rare events.
* **What changes against the global rule:** closed positive-gain sets leaving `D_0` are not chosen, so their flips are
  absorbed into the released SO(3) history. [Corrected in section 11.7: the following claim is false; a fixed fraction of minimal labels near the grid can be lost.] Those sets have an unflipped stretch longer than `M R_0` outside the flip
  cubes. Their probability is bounded by the Peierls sum of `REVIEW2-RESPONSE.md` 1, which is now only a fidelity
  statement, not a locality input. Whether this loss matters for observables belongs to N-2 (part 2).
* **Status: paper.** `REVIEW2-RESPONSE.md` 1's locality claim is replaced by this definition. Its Peierls bound
  (correct, REVIEW-3) is kept as a probability estimate.

## 6. Left for part 2 (done: sections 7-10)

* **H4:** R10's split on the positive partition, and the scale-`K` normalisation.
* **N-2:** density of the block-observable class in the limit, and the loss from sub-block flux erasure.
* **H3:** `S1-CURRENT.md` rewritten as the induction, with the order of constants, the window form (section 4.2), and
  the E-row for irregular coarse plaquettes from random swallowed bonds and fillings.
* **H7 and H8:** the remaining wording, the stale headers in `Assembly.lean`, `DECODER-LOCAL.md` 0 and `FILL.md` 0.4-0.5.

# Part 2 (m1-tools, 2026-11-22): H4, N-2, H3, H7, H8

## 7. H4: R10 on the positive partition

* **Agreed** (REVIEW-3 H4, follow-up G4 remark):
  * `E_D` is a summation index of Balaban's representation, not an event of `(V_K, τ')`;
  * R7 is a bare-scale normalisation and cannot turn per-cube factors at scale `K` into probabilities;
  * the class must be gauge invariant;
  * the constants also depend on `L_*/ℓ`.
* `WRITEOUTS.md` 2, step D, is replaced by the following. Steps A-C stay, for real `t` only.

**Setting.**
* `F` is a gauge-invariant character polynomial, of degree `≤ n`, in the block variables at scale `m` (`L^m a = ℓ`), on
  a region `A` of physical extent `R`, with `|F| ≤ 1`.
* Insert `e^{tF}` for real `|t| ≤ t_0(n, R/ℓ)` at scale `m`. The tilted measure is positive, so the conditional step
  is exact for it (`Exact.lean`, no complex densities needed), and `E[F | V_K, τ'] = ∂_t ρ_K^{(t)} / ρ_K` at `t = 0`.

**The positive partition.**
* At scale `K`, use Balaban's representation (1.104).
* For real `V`, every term is non-negative:
  * the characteristic functions and the `T(Y)1` are non-negative;
  * the action is real;
  * the label factors are positive ((P1), section 4).
* The large-field domains `Y_i` of a term, with their attached boundary terms Mayer-expanded into connected clusters,
  and the labelled fixed domains, form a polymer configuration with non-negative activities.
* Those activities are bounded uniformly in `V` by `e^{−p0(g_K)} e^{−κ d_K(Y)}` ([V] (1.89) improved, (1.99)).
* Let `N(A)` be the `L_*`-neighbourhood of the scale-`K` image of `A`. The **`A`-cluster** `G` of a term is the
  connected component of `N(A)` in the union of `N(A)` and the polymers of the term.
* `ρ_K = Σ_G ρ_G`, all `ρ_G ≥ 0`, and likewise `ρ^{(t)}_K = Σ_G ρ^{(t)}_G`.

**Where `t` enters.** Only in three places:
* the small-field action terms that descend from `tF` ([V] (1.59)-(1.62), (1.98)-(1.100)), local with
  `|Φ_t(X)| ≤ C |t| e^{−κ d_K(X)}`, `C = C(n, R/ℓ, L_*/ℓ)` since `K − m = log_L(L_*/ℓ)` steps are carried;
* the `T`-operations and label factors whose history met `A` at scale `m`. Their scale-`K` images meet `N(A)`, so they
  lie in `G`.

**Mixture formula.**
`E[F | V, τ'] = Σ_G P(G | V, τ') · ∂_t log ρ^{(t)}_G |_{t=0}`, with `P(G | V, τ') = ρ_G/ρ_K ≥ 0`, and
`∂_t log ρ^{(t)}_G = E[F | inner history of G, V, τ'] + Σ_X ∂_t Φ_t(X)`.
* The first term is a conditional expectation under a positive measure, so its modulus is at most 1.
* The second is local. By Cauchy in `t` it is bounded by `C t_0^{-1}` and, outside the `D/2`-neighbourhood of `A`, by
  `C e^{−κ D/(2 L_*)}`.

**Locality of the weights.**
* `P(G | V, τ') = a_G(V) Ξ_{−G}(V) / Ξ(V)`, where:
  * `a_G` is the product of the activities in `G`;
  * `Ξ`, `Ξ_{−G}` are the polymer sums, over all configurations and over those compatible with `G`.
* The activities are small uniformly in `V`, so the cluster expansion converges and
  `log(Ξ_{−G}/Ξ) = −Σ_{clusters meeting G}`, a sum of local terms with decay `e^{−κ d_K}`.
* Truncating to clusters inside the `D/2`-neighbourhood of `A` costs `C e^{−κ D/(2L_*)}` per `G`. The sum over `G` is
  controlled by the activities.

**Estimate.**
* Let `f` be the truncated mixture over non-crossing `G` (those inside the `D/2`-neighbourhood of `A`). It is a function
  of `(V_K, τ')` near `A`, with `|f| ≤ 1 + C`.
* Then `‖E[F | V_K, τ'] − f‖_{L¹} ≤ C e^{−κ D/(2L_*)} + (2 + C) P(G crosses)`, with `P(G crosses) = Σ_{G crossing} ∫ ρ_G`.

**The scale-`K` normalisation** (H4.2).
* `∫ ρ_G dν_K ≤ sup(a_G) · Z_{−G}/Z`, where `Z = ∫ ρ_K dν_K = 1` (a law) and `Z_{−G}` is the same integral with the
  region of `G` removed:
  * on the region of `G`, the Haar integral of the characteristic functions is `≤ 1`;
  * outside, the polymer sum compatible with `G` is `≤ Ξ`.
* **Lower bound for `Z`.** Restrict the variables on `G`'s region to the small-field set. There `ρ_K ≥ e^{A_K(V)} Ξ`,
  with `A_K` within `O(1)` per cube of the quadratic form `−(1/g_K²) Σ |V(∂p) − 1|²` (the bounds of [III] Sect. 2 on
  the effective action). The Gaussian integral over the region gives `≥ c g_K^3` per bond, so
  `Z_{−G}/Z ≤ (C β_K^{3/2})^{#bonds(G)} e^{O(1) #cubes(G)}`.
* **This factor is the normalisation of the top variables** on `G`: R7′ at scale `K`, `exp(O(1)(M R_K)^d log g_K^{-2})`
  per `M R_K`-cube. Balaban pays exactly this when his next step integrates a large-field domain's top variables. The
  normalisation constants, "`O(1) log g_j^{-2}|Z_j| ≤ O(1) M^d R_j^{d+1} d'_j(Z_j)`" before (1.89), come out of the
  large-field factors (`≥ p0` per cube, `p0 ≫ M^d R^{d+1}`) that the domain carries.
  * For the large-field domains in `G` it is paid from the same budget, as one more step within their lifetime.
  * Labelled domains in `G` are small-field: their top variables are Gaussian like the alternative's, so they need no
    such payment.
* **Hence** `∫ ρ_G ≤ e^{−2p0(g_K)} e^{−(κ − C) d_K(G)}`, with `d_K` in `M`-cubes, and
  `P(G crosses) ≤ Σ_{connected G from N(A) to distance D/2} e^{−(κ − C) d_K(G)} ≤ e^{−c κ D/(M L_*)}`
  (connected sets of `n` cubes number `≤ C^n`; Balaban's `κ` is chosen to beat polymer entropy).

**Covariance.** Insert `e^{sF}` at `A` and `e^{tG}` at `B`, at distance `D`. Then
`Cov(F, G | V, τ') = ∂_s ∂_t log ρ^{(s,t)}`. In the mixture, non-crossing configurations with disjoint `A`- and
`B`-clusters contribute only through clusters meeting both, `≤ C e^{−κ D/(2L_*)}`. Crossing ones contribute
`≤ 4 P(crossing)`. The same `L¹` bound holds.

**Result.**
`‖E[F | V_K, τ'] − f‖_{L¹} ≤ C(n, R/ℓ, L_*/ℓ) e^{−m D}` with `m = c κ/(M L_*)`, and the same for the conditional
covariance. **Status: paper**, on these citation-level inputs:
* the non-negativity of (1.104) for real fields;
* (1.89) with Balaban's normalisation constants, including the payment of the top variables' normalisation from the
  large-field budget, as in his next step;
* the two-sided small-field bounds of [III] Sect. 2 at scale `K`.

The cluster expansion of a positive polymer gas with uniformly small activities is standard.

## 8. N-2: is the block-observable class dense in the limit?

**The concern** (follow-up G4, N-2).
* M1's block state at scale `ℓ` forgets centre flux in vortices thinner than `ℓ` that are not kept as labels:
  * thick-born sheets erased once thinner than a block;
  * closed sets leaving the decoder's components (section 5).
* So the sign that such vortices give a fundamental Wilson loop is not a function of the block state.
* Whether their number linking a loop goes to 0 as `ℓ → 0` depends on the minimal action `c0/g²` of a closed Z2 sheet
  against `1/b ≈ 10.8`, which nothing in M1 bounds.

**Answer: density holds in the OS norm, whatever `c0` is. The comparison with `1/b` decides only `L²`-closeness, which
the spectral upgrade does not need.**

1. **What the upgrade needs.**
   * The reflection-positivity upgrade works in the OS space: vectors are positive-time observables `F`, with
     `‖F‖²_OS = E[θF̄ · F]`, where `θF̄` lives at the mirrored time.
   * A gap on a set of vectors dense **in this norm** gives the gap on the whole space.
   * `‖·‖_OS ≤ ‖·‖_{L²}` (Cauchy-Schwarz, `θ` measure-preserving), so OS density is weaker than `L²` density.
2. **The estimate.**
   * Let `F` be a bounded gauge-invariant observable supported in a region of extent `R` at time `≥ t > 0`. Let
     `f_ℓ` be the local approximant of section 7 at scale `ℓ`: a function of the block state at scale `ℓ` near
     `supp F`, at time `> t/2`. Put `R_ℓ := F − f_ℓ`.
   * Then `‖R_ℓ‖²_OS = E[Cov(θR̄_ℓ, R_ℓ | F_ℓ)] + E[E[θR̄_ℓ | F_ℓ] E[R_ℓ | F_ℓ]]`, with `F_ℓ` the block state at scale
     `ℓ`, everywhere.
   * The second term is `≤ C ‖E[F | F_ℓ] − f_ℓ‖_{L¹}`. The first is the conditional covariance of two observables at
     distance `≥ 2t` (`f_ℓ` drops out, being `F_ℓ`-measurable).
   * Section 7's argument at top scale `ℓ` bounds both by `C(F) e^{−c t/ℓ}`.
   * Uniformity in the spacing: the clusters at scale `j < ℓ` contribute `(R/(L^j a))^d e^{−κ t/(L^j a)}`, summed over
     `j`, dominated by the top scale.
   * So `‖F − f_ℓ‖_OS → 0` as `ℓ → 0`, uniformly in `a`.
3. **Why the erased vortices do not matter.**
   * A vortex thinner than `ℓ` that links `C` but not `θC` changes the sign of `W(C)` independently of everything at
     distance `≫ ℓ`, given the block state. It drops out of `E[θR̄ R | F_ℓ]` (conditional decorrelation).
   * What could survive is a single vortex linking both `C` and `θC`: size `≥ 2t`, thickness `< ℓ`. Its action is
     `≳ c0 (t/ℓ)²/g²`, so it is a crossing term of section 7, `≤ e^{−c t/ℓ}`.
   * Whether `c0 b > 1` decides only whether `W(C)` is `L²`-close to its proxy. If `c0 b < 1`, the unrenormalised
     `W(C)` has a vanishing limit and the renormalised one is covered by item 2, since renormalisation is a constant
     factor.
4. **From `f_ℓ` to the class `𝒟_ℓ`.**
   * `f_ℓ` is a function of finitely many compact block variables, `(R/ℓ)^d` of them.
   * On small-field configurations it is analytic, with bounds uniform in `a` (Balaban's domains); large-field
     configurations carry mass `≤ e^{−c p0}` per cube.
   * So `f_ℓ` is approximated in `L²(law)`, uniformly in `a`, by gauge-invariant character polynomials of bounded
     degree (Peter-Weyl on the small-field set). The OS norm is dominated by the `L²` norm.
5. **The Wilson-loop formula of `REVIEW2-RESPONSE.md` 4** (REVIEW-3 H8, follow-up G5) is corrected.
   * The block-state proxy of `W(C)` is `(Π_{p ∈ S} τ'_p) · ½ tr(Stokes lift over S of V_ℓ)`: lift each coarse
     plaquette holonomy near 1, then compose (non-abelian Stokes with continuous lifting).
   * It is not "the lift of `Hol_V(C)`", which is ambiguous for loops of physical size.
   * It is defined where the coarse plaquettes on `S` are regular. Elsewhere the proxy is any bounded function; that set
     has small mass.

**Status:**
* **Paper sketch.**
  * Item 2 uses section 7 at top scale `ℓ` for bounded fine observables. Their small-field part needs the conditional
    fluctuation measure as a polymer gas with `V`-dependent activities (Balaban's representation at each scale below
    `ℓ`), with `|⟨F⟩_V − ⟨F⟩_{V'}|` bounded by the clusters linking `supp F` to where `V ≠ V'`. Standard in form, not
    written line by line.
  * Item 4's uniform polynomial approximation is a sketch.
* **For the interface:** `MassGapLoc` should be stated for the OS closure of bounded local gauge-invariant observables.
  The physics question `c0` versus `1/b` is not needed.

## 9. H3: the induction

Written in `S1-INDUCTION.md`, which supersedes `S1-CURRENT.md`. Labels are as in section 11:
* the order of constants;
* `Form_k` with its bounds, including the window form;
* the step as eleven operations, each with input, output, what it uses and its level;
* the new E-row: the large-field factor for coarse plaquettes whose blocks meet a hole, including the randomised
  swallowed bonds and fillings, taken from the deep set's action.

## 10. H7, H8 and stale text

* **H7.1-H7.3:** in the `WRITEOUTS.md` update note (part 1).
* **H7.4:** in section 1.2 (`16 b(1 − δ)`, `δ = p0²/β`).
* **H7.5:** the label bound uses `g_j` at the release scale. `e^{−16/g_j²}` versus `e^{−16/g_0²}` differ by
  `e^{16 b log L · j}` with `j ≤ R_0 + n0`, a `poly(g^{-2})` factor, absorbed by the margin `16 b(1 − δ) > 1`.
* **H8:**
  * tie-break lexicographic (section 5, `CLOSING.md` note);
  * Wilson-loop formula corrected (section 8.5);
  * martingale density replaced by section 8.
* **Stale text:**
  * `Assembly.lean`'s module docstring and two field docstrings now name the current design and `S1-INDUCTION.md`
    (no code changed; rebuilt, see the axioms log);
  * `DECODER-LOCAL.md` 0 and `FILL.md` 0.4-0.5 carry update notes (part 1);
  * `M1-PLAN.md` 0 rows updated.

## 11. Labels after the part-1 follow-ups (REVIEW-2 second follow-up, REVIEW-3 follow-up, the owner's reading)

**Agreed, all six points:**
1. section 4.4's carrying sum was undercounted: a label on the deepest skeleton lives up to `K` steps in a domain of
   at least one cube, and the attached clusters cost `c1` per step;
2. (1.103) covers only the one-step expansion. Balaban's fixed domains stay large-field, while released labelled
   domains are integrated in later small-field steps;
3. the real fluctuation was compared, contrary to section 4.3's wording;
4. `Φ ∘ U_bg` is not local;
5. the threshold must be Balaban's small per-domain factor `ε_*`, not `1/4`;
6. carrying large components beyond the lifetime is sketch, not citation.

**The repair restores R8 for labels, as the reviewers and the owner's reading ask.** Once its constant is split off,
a small released label is a small local analytic term with an index. Its field dependence is dimension 4 at a point,
which is **irrelevant**: it shrinks by `L^{-4}` per step. So the per-step cost is summable, uniformly in how long the
label lives.

### 11.1 The form at release (small components, `δ_k |X| ≤ ε_*`)

* **(P2) on the whole analyticity domain.**
  * Balaban expands the integrand of (1.71) "up to the first order in `A'`, `J`" ([V] p. 379). Here `A'` is the real
    deviation of the configuration from the regular base and `J` its complex part.
  * So the positivity argument of section 4.3 applies to real and complex deviations alike: for `V` in the domain
    `U_k(X, α_0, α_1)` around a base `U`, `Φ_ℓ(V) = Φ_ℓ(U)(1 + η)` with `|η| ≤ e^{sup|Δ|} − 1`.
  * **Wording corrected:** real deviations within the domain *are* compared, through `A'`.
  * **Reading to check against the text** (with the per-cube question): `A'` ranges over the real small-field
    deviations, as the REVIEW-2 reviewer also reads it.
* **Base = flat, patch by patch.** After the localisation of 11.3, each piece depends on `V` in a region of bounded size.
  There, in an axial gauge, every small-field configuration lies within `C ε_k ≤ α_0` of the identity, so the flat
  configuration serves as base.
* **The form.** `Φ_ℓ(X; V) = a_ℓ e^{L_ℓ(V)}`, where:
  * `a_ℓ := Φ_ℓ(X; flat)` is a constant;
  * `L_ℓ` is analytic, gauge invariant, `L_ℓ(flat) = 0`, with `|L_ℓ| ≤ 2 δ_X` on the domain and `δ_X := sup|Δ| ≤ ε_*`.
* **No linear coupling (R8).** At the flat configuration, gauge invariance and the absence of an `Ad`-invariant vector
  in `so(3)` give `dL_ℓ = 0`. So on real small fields `|L_ℓ(V)| ≤ C δ_X Σ_{p near X} |F_p|²/α_1²`, with `F_p` the
  curvature (`CLOSE-OUT.md` 2, Cauchy estimates in the domain).
* **This is REVIEW-3 H1's requested form** `a_ℓ (1 + h_ℓ)`, `h_ℓ = e^{L_ℓ} − 1` small. It is now derived, for small
  components, from (P2) on the full domain plus R8, instead of asserted.

### 11.2 What a labelled domain is in later steps, and what each step costs

* **What it is:** for `k' >` release, a labelled domain is neither a large-field domain nor an E- or R-term of
  Balaban's covariant sums. It is a **constant `a_ℓ` times `exp` of an indexed local term `L_ℓ`** at a fixed position.
  It carries no characteristic function and no hard core: the other polymers are not excluded from its domain.
* So no boundary terms are re-created at each step, and **no `c1` per step**. The one-time boundary terms from the
  release expansion (B′-terms meeting `X`, bound `c1 e^{−κ d}`) are absorbed into `a_ℓ` and `L_ℓ` once.
* **Step `k' → k' + 1`.** `V_{k'} = U_bg(V_{k'+1}) e^{i g_{k'} B}`, and `L_ℓ` depends on `V_{k'}` through the background
  map down to the release scale.
  * Curvature at the release scale is the curvature at scale `k'` times `L^{−2(k' − k_r)}`, in the label's own units.
  * By 11.1, `L_ℓ ∘ (background) = O(δ_X (ε_{k'} + g_{k'})² L^{−4(k' − k_r)}/α_1²)`, uniformly on the next fluctuation
    domain.
  * The fluctuation integral of `e^{L_ℓ}` gives `exp(log⟨e^{ΔL_ℓ}⟩)`, a cumulant series in a small local quantity. It
    splits into:
    * a constant, which goes into `a_ℓ` (the label's self-energy);
    * a local gauge-invariant term with no linear coupling, which is the new `L_ℓ`.
  * Both are `O(δ_X (ε_{k'} + g_{k'})² L^{−4(k' − k_r)})`.
* **Summable over the whole life.** `Σ_{k' ≥ k_r} δ_X (ε + g)²_{k'} L^{−4(k' − k_r)} ≤ C δ_X (ε + g)²_{k_r}`.
  * This is independent of how long the label lives, so the deepest skeleton labels are covered uniformly.
  * `a_ℓ` changes by a factor `e^{O(δ_X)}` in total.
  * The linear-in-`K` term of the follow-ups does not arise, because the attached part is `L_ℓ` itself, which shrinks.
    Section 4.4 was missing exactly this R8 step.
* **Thin components** (REVIEW-3 follow-up, NIT 5): the domain's own size shrinks like `L^{−1}` or `L^{−2}` per step,
  not `L^{−4}`. The field dependence still shrinks like `L^{−4}`, because the coupling is at a point once the domain is
  below a cube. All sums stay geometric.

### 11.3 Localisation of `Φ ∘ U_bg` (point 4)

* The background is non-local, with exponentially decaying dependence ([15] (190), the `H`-functions).
* Write `L_ℓ(U_bg(V))` by Balaban's telescoping localisation, the one he applies to every E-term ([V] (1.59)-(1.63),
  pp. 374-376): the background computed from `V` restricted to the `r`-neighbourhood of `X`, plus differences between
  radii `r` and `r + 1`.
* Each difference is `≤ |∂L_ℓ| e^{−κ r} ≤ C δ_X (ε/α_1) e^{−κ r} L^{−2(k' − k_r)}` (by 11.1 and the decay).
* So `L_ℓ` is a sum of local terms with decay, of the same class as Balaban's E-terms but at a fixed position.
* **Citation-level adaptation.**

### 11.4 Large components and the threshold (points 5, 6)

* **Threshold:** `δ_k |X| ≤ ε_*`, with `ε_*` the smallness Balaban requires of a fixed-domain factor ((1.93):
  `ε^{1/3} ≤ exp(−(1 + β) 2d)`). Since `δ_k → 0`, this only moves the case split. Under the per-component reading of
  REVIEW-3's follow-up, every component is small once `δ_k ≤ ε_*`.
* **Components above the threshold** are carried as large-field regions beyond Balaban's lifetime until their image is
  below it. That needs his entropy induction re-run, as for R2's footprint-weighted lifetime: **sketch**, not citation.
  Under the per-component reading it is empty.

### 11.5 The owner's reading, checked

* **Does the attached part shrink at every step, uniformly, including the deepest skeleton labels?** Yes: by
  `L^{−4(k' − k_r)}` times `(ε + g)²_{k'}` (11.2). It does not depend on the label's lifetime; only on the steps since
  its release.
* **Should the remainders go into the running coupling?** No, and they do not need to.
  * The remainders of a label (11.2) are localised at the label's point. Their constant part renormalises the label's
    own weight `a_ℓ`; their field part is an irrelevant point term that shrinks by itself.
  * Absorbing them into the coupling would add a position-dependent `F²` term. [I] Theorem 2 fixes the running of a
    uniform coupling and does not cover that. **So absorbing them would change the running, and the repair does not
    do it.** [I]'s input is untouched.
  * What does go into the coupling and the vacuum energy is what always did: the bulk small-field terms, together with
    the released large fields' R-terms (R8 for acts).
* **"Two ticks":** the label is extracted at release. The next step integrates its first-order remainder (the generic
  `δ_X` part, now small because of the threshold) and leaves only the shrinking dimension-4 term. This matches the
  reading in substance. The difference is where the remainder goes: to the label's own constant, not to the coupling.

### 11.6 Status

* **Paper:** the argument of 11.1-11.2. It rests on three citation-level adaptations:
  * (P2) on the full domain, real `A'` included (reading to check);
  * Balaban's localisation for 11.3;
  * small-field steps accepting a small, gauge-invariant, indexed local term within his E-term bounds. The term is not
    renormalised through covariance; its constant is moved into `a_ℓ` by hand.
* **Sketch:** components above `ε_*` (11.4).
* **Form in `Form_k`:** a hard-core polymer sum over labelled domains (`S1-INDUCTION.md` (F6)).
* **The REVIEW-3 H1 GAP is closed** for small components, at the level stated, with two text readings to check (per
  cube or per component; the range of `A'`).

### 11.7 Minor items from the follow-ups

* **H2 fidelity (REVIEW-3 follow-up).** The claim in section 5, "lost sets have an unflipped stretch longer than
  `M R_0`", is **false**.
  * A minimal bubble with its flips in one cube and one unflipped plaquette in the next cube is lost.
  * The local decoder can lose a fixed fraction of minimal labels near the grid, possibly most skeleton labels if the
    grid is aligned with the block lattice.
  * Law and counts are unaffected.
  * **For N-2 (section 8):** these lost labels are sub-`ℓ` structures, local noise that drops out of reflected
    pairings. Only closed sets of size `≥ 2t` could matter, and those are crossing terms. **The OS-density argument is
    unchanged.**
  * An optional fidelity fix: enlarge `D_0` by one layer of cubes. That keeps locality if Balaban's `Z_0` cover
    contains the layer, which I have not checked. Not adopted.
* **H5 constants (REVIEW-3 follow-up, NIT 2).** The data around a twist-free hole deviate from pure gauge by up to
  `C_tw r0 λ² ≈ 64 C_tw C_1² c L^{−2}`. The Dirichlet gap on a hole of diameter `≤ 2 C_1 L` is `≥ c'/(4 C_1² L²)`. So
  the filling closes for `c ≤ c'/(256 C_tw C_1^4)`, and E7.J's `‖E‖ ≤ C C_tw C_1² c ≤ ½` likewise.
  * The order of constants is `L`, `C_1`, `C_tw`, then `c` in `r0 = c/L⁴` (`S1-INDUCTION.md` 1).
  * `FILL.md` 3's `C c L^{−3}` is replaced by this.
* **H5 inequality (NIT 1).** A failing loop gives `θ > C_tw r0 |γ|²`, not `> C_tw r0 λ²`. Since a linking loop has
  `|γ| ≥ 12`, `θ > 144 C_tw r0 ≥ 4 ε_{k+1}`, and the conclusion stands. Section 2 item 2 is corrected.

## 12. Labels in one-box form (the owner's correction on "two ticks")

The owner's reading (`../../PREP.md`, last entry): the two ticks belong to the **parent**, the closed Z2 remainder the
label is released from. This gives (a) a persistence rule and (b) a one-box, one-step contraction. Both are worked out
below. Section 12.2 replaces the series of 11.2 by an iterated contraction; the estimate is the same, stated per step.

### 12.1 (a) Only a remainder that persists across two consecutive scales is a label

* **Persistence in M1 terms.** A closed remainder `S` chosen by the decoder appears in `τ'_0`. It appears in `τ'_1`
  only if it is linked with the scale-1 coarse 1-skeleton, which is the only way a closed set feeds a coarse bit
  (`CLOSING.md` 2). In general it appears in `τ'_j` exactly for `j ≤ j(S)`, where `j(S)` is the coarsest scale whose
  skeleton carries a bond linked with `S`. The skeletons are nested, so the scales at which it appears are consecutive
  from 0.
* **The rule.** A remainder with `j(S) = 0` (seen at one scale only) is not a label.
  * It is summed over with the rest of its large-field region and released into R-terms, like a lone act.
  * It does not change any `τ'_k` with `k ≥ 1`, so nothing in the coarse laws distinguishes it.
  * At scale `k`, only remainders with `j(S) ≥ k` are indexed. When a step passes `j(S)`, the label no longer affects
    `τ'_{k+1}`. It is summed out at that step: its factor `a_ℓ e^{L_ℓ}` is summed over its index together with the
    unlabelled gas and exponentiated into R-terms. Its life ends where its parent stops persisting.
* **Effect on the decoder.** None. The decoder's chosen set (positive-gain closed sets per flip-cube component) is the
  same. Only which chosen sets are carried as indexed labels at a given scale changes.
* **Effect on the count.** None that hurts.
  * The count of `CLOSING.md` 2 already counts only skeleton-linked remainders: per scale-`k` coarse bond,
    `e^{−16(1−δ)/g_k²} L^{(1−16b(1−δ))k}`.
  * The rule removes the `j(S) = 0` remainders, which were never counted at `k ≥ 1`.
  * Upper bounds only decrease.
* **Consistency.** It is measurable: `j(S)` is a lattice-geometric function of `S`. It also matches the law: at the
  step `j(S) → j(S) + 1` the label's index stops being a variable of the law, so summing it out is exact.

### 12.2 (b) One box, one step: the contraction lemma

**Setting.**
* A small released label (`δ_X ≤ ε_*`) carried at scale `k ≥ k_r` is `a^{(k)}_ℓ e^{L^{(k)}_ℓ}`.
* `L^{(k)}_ℓ` is localised at the scale-`k` cube `Q_k` containing the label's point (11.3), with tails weighted by
  `e^{κ dist}`.
* Its **cost on the box** is `N_k := sup |L^{(k)}_ℓ|` over Balaban's analyticity domain at scale `k`, restricted to
  `Q_k`: curvature `≤ α_1` in scale-`k` units, tails weighted as stated.

**Lemma (one-box contraction).** There is `C`, depending only on Balaban's constants at fixed `L`, such that if
`N_k ≤ ε_1 := L^{-4}/C` then
* `N_{k+1} ≤ θ N_k`, with `θ := C L^{-4} ≤ ½`;
* `|log a^{(k+1)}_ℓ − log a^{(k)}_ℓ| ≤ C N_k`.

**Proof.** One RG step: `V_k = U_bg(V_{k+1}) e^{i g_k B}`, and
`a^{(k+1)}_ℓ e^{L^{(k+1)}_ℓ(V_{k+1})} = a^{(k)}_ℓ ⟨e^{L^{(k)}_ℓ(V_k)}⟩_B`,
with `⟨·⟩_B` Balaban's normalised fluctuation measure at fixed `V_{k+1}`.
1. **No linear term (R8).** `L^{(k)}_ℓ` is gauge invariant, vanishes at the flat configuration, and `so(3)` has no
   `Ad`-invariant vector. So its expansion in the curvature `F` on `Q_k` starts at second order. Cauchy estimates on the
   domain give `L^{(k)}_ℓ = Q(F) + R_3(F)`, with `Q` quadratic, `|Q(F)| ≤ N_k (|F|/α_1)²` and `|R_3(F)| ≤ C N_k (|F|/α_1)³`.
2. **Split the curvature:** `F = F_bg + F_fl`, background and fluctuation, both in scale-`k` units on `Q_k`. Then
   `⟨e^{L}⟩_B = exp(Q(F_bg) + ⟨Q(F_fl)⟩ + ⟨2Q(F_bg, F_fl)⟩ + (cumulants) + ⟨R_3⟩)`.
3. **What goes to the constant (the first tick of the box):** `⟨Q(F_fl)⟩` and the `F_bg`-independent cumulants, all
   `≤ C N_k`. They become `log a^{(k+1)} − log a^{(k)}`.
4. **What is left, the dimension-4 residue (the second tick):**
   * **Nothing linear in `F_bg`.** A term linear in `F_bg` is a gauge-invariant function linear in an adjoint-valued
     quantity at a point. There is none (item 1 again). So `⟨2Q(F_bg, F_fl)⟩` and the linear parts of the cumulants
     vanish identically, not just on average.
   * **Quadratic and higher in `F_bg`:**
     * `Q(F_bg)`;
     * the `F_bg`-dependence of the higher cumulants, `≤ C N_k² (|F_bg|/α_1)²`;
     * `⟨R_3⟩`, whose `F_bg`-dependent part is `≤ C N_k (|F_bg|/α_1)²(|F_bg| + g_k)/α_1`.
5. **Rescale to the new box.** The background on `Q_k` is the interpolation of `V_{k+1}`. Its curvature in scale-`k`
   units is `L^{−2}` times the curvature of `V_{k+1}` in scale-`(k+1)` units ([15]; the background scales as a
   dimension-2 field). On the scale-`(k+1)` domain that curvature is `≤ α_1`, so `|F_bg| ≤ L^{−2} α_1 (1 + o(1))`.
6. **Hence**
   `N_{k+1} ≤ N_k (L^{−4} + C N_k L^{−4} + C L^{−6} + C L^{−4} g_k/α_1) + (localisation tails) ≤ C L^{−4} N_k`.
   The tails of 11.3 add `C e^{−κ} N_k` to the weighted norm and are absorbed into `C`.
7. **The constant changes by at most `C N_k`** (item 3). ∎

**Iteration over the label's life.**
* At release, `N_{k_r} ≤ 2 δ_X ≤ 2 ε_*`. Choose `ε_* ≤ ε_1/2`, a condition on Balaban's threshold at fixed `L`, added
  to `S1-INDUCTION.md` 1.
* The lemma then applies at every step, so `N_{k_r + n} ≤ θ^n N_{k_r}`.
* The weight changes in total by `exp(C N_{k_r}/(1 − θ)) ≤ e^{4C ε_*}`, whatever the life length.
* This covers the labels on the deepest skeleton, which live until `j(S)`, possibly `K`: the bound does not depend on
  the number of steps.
* **No global series is summed:** the one-box, one-step contraction is iterated, as in the owner's reading.

**What "handed to the coupling" means here.**
* In the box, the first-tick remainder goes into the box's own constant: the label's weight `a_ℓ`, its self-energy.
* It does **not** go into the bulk running coupling. That would be a position-dependent `F²` term, which [I] Theorem 2
  does not cover (11.5).
* So the owner's "the coupling becomes more efficient" holds for the label's own coupling to the field: the residue
  shrinks by `θ` per step. [I]'s running is untouched.

### 12.3 Status

* **12.1:** paper.
* **12.2:** paper. The lemma's inputs are the same citation-level adaptations as in 11.6:
  * (P2) on the full domain with real `A'`;
  * Balaban's localisation;
  * the fluctuation measure's analyticity and bounds at scale `k`;
  * the dimension-2 scaling of the background ([15]).
* It replaces 11.2's series; 11.1, 11.3, 11.4 and 11.5 stand.
* Components above `ε_*` remain **sketch** (11.4).
