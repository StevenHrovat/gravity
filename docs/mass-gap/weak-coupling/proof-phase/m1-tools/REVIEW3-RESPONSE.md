# Response to REVIEW-3 and the REVIEW-2 follow-up, part 1 (m1-tools, 2026-11-22)

Brief (coordinator): `../m1-review/REVIEW-3.md` and `../m1-review/REVIEW-2-FOLLOWUP.md` agree that the verdict
"complete at paper level" overstates what is written. Order: N-1, H5 and H6 first, then H1, H2, H4, N-2, H3. Report
after H1 and H2. Stop at anything fatal or much harder than marked. Correct the verdict in `M1-PLAN.md` 0 to what is
written. Claim marks as in `NOTE.md`.

This part covers N-1, H5, H6, H1 and H2. H4, N-2, H3, H7 and H8 follow in part 2.

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
     `ℓ_max ≥ C L` of `H_0`, with SO(3) twist `θ > C_tw r0 λ² ≥ 4 ε_{k+1}`. By `FILL.md` 0.2, the averaged coarse loops
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
  absorbed into the released SO(3) history. Those sets have an unflipped stretch longer than `M R_0` outside the flip
  cubes. Their probability is bounded by the Peierls sum of `REVIEW2-RESPONSE.md` 1, which is now only a fidelity
  statement, not a locality input. Whether this loss matters for observables belongs to N-2 (part 2).
* **Status: paper.** `REVIEW2-RESPONSE.md` 1's locality claim is replaced by this definition. Its Peierls bound
  (correct, REVIEW-3) is kept as a probability estimate.

## 6. Left for part 2

* **H4:** R10's split on the positive partition, and the scale-`K` normalisation.
* **N-2:** density of the block-observable class in the limit, and the loss from sub-block flux erasure.
* **H3:** `S1-CURRENT.md` rewritten as the induction, with the order of constants, the window form (section 4.2), and
  the E-row for irregular coarse plaquettes from random swallowed bonds and fillings.
* **H7 and H8:** the remaining wording, the stale headers in `Assembly.lean`, `DECODER-LOCAL.md` 0 and `FILL.md` 0.4-0.5.
