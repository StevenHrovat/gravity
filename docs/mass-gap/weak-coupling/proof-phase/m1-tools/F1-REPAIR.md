# REVIEW-1: assessment of F1-F6, and a repair attempt for F1 (m1-tools, 2026-11-22)

Brief: `../m1-review/REVIEW-1.md` (committed 435e56c) finds the estimate half of M1 broken (F1, fatal) and lists
gaps F2-F6. Tasks: say for each finding whether it holds; look for a repair of F1, starting from the owner's reading
(`../../PREP.md`, "The fourth dimension is what M1 is missing": a record holds only for its own transition, then is
released, leaving only its loss) and the coordinator's note (released records absorbed into the effective action as
local terms); consider a scale-dependent threshold and what vortex persistence (`Vortex.lean`) still forces. Report
before building anything large. Read for this note: REVIEW-1; PREP's last entry; `Vortex.lean`; [III] pp. 259-260
((2.30)-(2.33), the R-terms and their summation over scales). Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **The review is right on F1-F6.** F1 is fatal for the design as written, and it was my error: `TRAP.md` 3 took
   the root count of `D-PIN.md` (cores pinned at nested block centres: one position per cell per scale) and applied it
   to trapping, which traps every deep plaquette anywhere. F2-F6 are real gaps. Section 1 gives the reasons.
2. **F1 splits into two problems, and only one of them is repaired here.**
   * **Counting: repairable.** Only cores at nested block centres need to be held. `Vortex.lean` shows exactly these
     persist under every covariant, rotation-symmetric blocking, the excised blocking included. Every other deep core
     needs no record. It is excised for one step (so the fibre-mass bound E7.J needs only its easy version); its
     content becomes an ordinary large-field integration variable inside Balaban's `T`-operations; and it is
     renormalised away after Balaban's delay. That is the owner's "released, leaving only its loss": the loss becomes
     one of Balaban's R-terms, and his R-term bookkeeping ([III] (2.30)-(2.33): vacuum energy subtracted, the
     remaining terms marginal, summed over scales "controlled by g") already handles R-terms born densely at every
     scale. With records only at nested centres the per-cell count is `e^{-A/g_k²} Σ_j L^{-bAj}`, which converges for
     every `A > 0`.
   * **Persistent centre cores: not repaired; this is what blocks.** A core held at nested centres is a non-regular
     region of the block field at **every** coarser scale (`Vortex.lean`: a −1 coarse plaquette, scale-invariant). In
     the law it cannot be integrated away, so Balaban's bounds charge it the large-field carrying cost per step,
     `O(M^d R^{d+1}) = polylog(g^{-2})`. What the flow frees per step is only `b c_v log L`: asymptotic freedom times
     the scale-invariant action `c_v` of a −1 coarse plaquette. Since `polylog(g^{-2}) ≫ b c_v log L`, the summed
     carrying cost beats the record's suppression (this is F2's divergence, in its sharpest form).
3. **What would unblock it** (new, not routine; section 4). A small-field theory around a vortex background: a
   Gaussian fluctuation theory and a constrained minimiser in the twisted sector, a `[15]`/`[13]` analogue around a
   thick −1 flux. It would replace the polylog per step by an `O(1)` per-step cost `C_1`, and the record then closes
   if the **rate condition** `b c_v log L > C_1` holds. That is D-PIN's P3, coming back as the reviewer predicted. It
   is the owner's "only its loss" made quantitative: per step a persistent vortex must cost less than the running
   coupling frees.
4. **A scale-dependent threshold does not help the counting.** Balaban's own large-field regions (threshold
   `g_j p0(g_j)`) are also dense in physical units; what saves him is release (renormalisation after the delay), not
   rarity. A fixed `r0` is fine for the released cores; for the persistent ones the relevant quantity is `c_v`, not
   `r0`.
5. **Recommendation:** do not build further on TRAP. The next step is the owner's decision, between:
   * (a) attempt the vortex-background theory and the rate condition (large: comparable to `[15]` plus parts of
     `[13]`);
   * (b) look for a reformulation in which centre cores need not be held in the law at all (for example, laws of a
     coarser observable that does not resolve the vortex's position).

## 1. The findings

| finding | verdict | reason |
|---|---|---|
| **F1** records dense | **agree, fatal** (for TRAP as designed) | The count is right: per scale-`k` cell, `Σ_j L^{dj} e^{-A/g_{k-j}²} = e^{-A/g_k²} Σ_j L^{(d-bA)j}`, which converges only for `bA > d` (`A ≳ 43`); M1's `A ~ L^{-8}`. My error: TRAP inherited D-PIN's per-cell count (one nested-centre position per scale), but trapped every deep plaquette everywhere. |
| **F2** Bianchi halo | **agree** | For a 3-cube containing a deep plaquette `p` whose flux does not close inside the hole, the other five faces carry angle `≥ θ_p` in total, in every configuration. So some neighbour of the frozen hole has angle `≥ r0/5` for ever, and the "decoupled" phase is never reached. My F5 justification in `S1-ROWS.md` ("regular because `Λ` is small-field") was a non sequitur: the small-field test is made on the excised block field, which never sees the frozen content. |
| **F3** P2′ Lemma E | **agree** | (i) At `ρ ~ 1` the claimed change `p0 (Cn)^{1/2}/g` is `≫ 1`, i.e. outside the analyticity domains where Cauchy estimates hold. (ii) `[15]` (9)-(10) bound the minimiser on cubes, not the linear response; the response is `[15]` (46), whose gradient bound I cannot confirm to be as smooth as Lemma B uses. Under the repair P2′ is not needed (section 3). |
| **F4** filling with `r0`-size data | **agree** | By F2 the data next to a fresh hole contain `~ r0/5` plaquettes, not `ε`. T1 uniqueness and E7.J's loop bound then need `r0 ≤ c/L⁴` (or a maximum principle). The rule for coarse bonds whose blocks lie inside a hole is missing. Still needed under the repair (excision stays): take `r0 = c/L⁴`, and add an explicit rule for swallowed blocks (open). |
| **F5** D-mod off-centre | **agree** | Only the block-centre contraction is proved; the off-centre step is numerical (`offcentre_L13.py`). Under the repair this is a needed lemma: off-centre cores (excised, then moderate) must dilute within Balaban's delay. Likely provable with the explicit path fractions and the BCH bound of `ROUTINE-ROWS.md` 4, but not done. |
| **F6** P4 citation | **agree** | `[15]` Theorem 1 states no lower bound of the action by block plaquettes and needs small data. The bound behind [V] (1.76) is presumably [16] (71), which I have not read. Under the repair P4 is not needed: released cores are Balaban large-field regions and pay his `exp(-p0)` factor, as in his own scheme. |
| F7 Lean assembly | agree (presentation) | The machine-checked core is `Exact.lean`; the assembly theorems are induction over named hypotheses and should be presented as bookkeeping, not as "the logical structure is machine-checked". |
| F8 smaller points | agree | Branch labels (a)/(b) are reversed in `S1-PROOF.md` 2; the rate (0.31) of [I] belongs in `EXTERNAL.md` row 1; three constant conditions are missing; the factor 2 in F3 of `S1-ROWS.md`; T2 needs a symmetric selection outside uniqueness. |

## 2. Why F1 happened, and what the counting really requires

* **Balaban's large-field regions are dense too.** A large-field region at scale `j` has weight `≈ e^{-p0(g_j)}` per
  scale-`j` cube, and a scale-`k` cell has `L^{d(k-j)}` such cubes. So per physical cell they are far denser than
  M1's records. Balaban never carries them for ever: after the delay `N` each is renormalised into R-terms
  ([V] (1.98)-(1.100)), and the R-terms are summed over scales by [III] (2.30)-(2.33). The vacuum energy (a constant)
  is subtracted, the remainder is marginal, "the sum over `j` is controlled by `g`". So the density of events in
  physical units is harmless if the events are released into the effective action.
* **Why release works for gauge-invariant local terms** (the coordinator's guess, made precise). A released term is a
  gauge-invariant local function `f` of the block field near its position. At a flat field its differential is
  invariant under constant gauge rotations, and `su(2)` has no non-zero invariant vector, so `df = 0`. Its field
  dependence therefore starts at second order in the curvature: a dimension-4 term, whose coefficient per physical cell
  from events born `j` scales below is `L^{dj} · L^{-4j} · e^{-A/g_{k-j}²}`, summable for every `A > 0` in `d = 4`.
  The reviewer's divergent `Σ L^{(2-bA)j}` used the capacity term `ρ^{d-2}` of a **frozen** hole (a Dirichlet
  condition breaks gauge invariance); once the content is integrated, that term is gone. (Paper-level argument;
  Balaban's own R-term bookkeeping is the rigorous version, and the released cores are R-terms of his type.)
* **What cannot be released: persistent cores.** `vortex_persists` needs only gauge covariance (including the flip by
  a central element at the coarse site), conjugation covariance and rotation equivariance of the blocking. The excised
  blocking with a covariant, symmetric filling has these (`TRAP-CHECKS.md` T2). So **excision does not remove a centre
  vortex.** Geometrically, the twist sits in the data loops around the hole, and the filling must reproduce it. Only a
  blocking that breaks the flip covariance (the Z2 labels of `TWIST.md`) hides it, and then the label carries it. At
  off-centre positions the symmetry argument fails, and the numerics (`offcentre_L13.py`) show deep cores diluting
  after one step.

## 3. The repaired design for the counting (paper sketch)

1. **Excise at creation, for one step.** Every plaquette of `V_h` at angle `≥ r0` (`r0 = c/L⁴`, F4) is excised from
   the block average `h → h + 1` (per-block filling). The constrained variables are then sub-`r0`, so E7.J holds in its
   easy form. The excised content stays an integration variable of Balaban's `T`-operation for its large-field region
   (excised variables enter no δ-constraint; Haar integrals over them are `≤ 1`, as Balaban's group integrals are).
2. **No record for off-centre cores.** If the core is not at a site of `T^{(h+1)}`, nothing is kept. The region (core,
   Bianchi halo) is an ordinary Balaban large-field region. Its block image is moderate (off-centre dilution, F5
   lemma needed) and becomes regular within the delay (D-mod), and Balaban's R-operation (with M1's conditional step
   for laws) renormalises it into R-terms. This is the "release": the record lives one step, its loss is an R-term.
3. **Records only for centre cores, only while they sit at nested centres.** A core at a site of `T^{(h+1)}` persists
   one step. At the first scale at which it is off-centre, it is released as in 2. Count per scale-`k` cell: one
   position per root scale, `Σ_h e^{-A/g_h²} = e^{-A/g_k²}/(1 - L^{-bA})`, finite for every `A > 0`. **F1's counting is
   repaired.**
4. P2′ and P4 are no longer needed for released cores (Balaban's own large-field accounting applies). For held centre
   cores they are replaced by the problem of section 4.

**Status of section 3:** paper sketch. Needed lemmas, all plausible but **not proved**:
* the off-centre dilution with BCH corrections (F5);
* "a released region becomes regular within the delay" (dilution or growth to a deep core);
* T1/T4 with `r0 = c/L⁴` and Bianchi-halo data;
* the rule for swallowed blocks.

## 4. What blocks: persistent centre cores

* **Cost per step.** A centre core held from scale `h` to `k` is a −1 coarse plaquette (non-regular) at every scale in
  between. In Balaban's framework a non-regular region of the law is a large-field region carried each step at
  `O(1) M^d R^{d+1}` (polylog in `g^{-2}`); [V] p. 380, confirmed by the reviewer.
* **What the flow frees per step.** The effective action's background term telescopes:
  `g_m^{-2} A(U_m) - g_{m+1}^{-2} A(U_{m+1}) ≥ (g_m^{-2} - g_{m+1}^{-2}) A(U_{m+1}) ≈ b log L · c_v`, with `c_v` the
  minimal action of a −1 coarse plaquette (scale invariant in four dimensions). This is all the suppression the
  persistent core supplies per step without using the same action twice.
* **The comparison fails.** `b c_v log L` (a constant) against `polylog(g_m^{-2})` (growing as `g → 0`): carrying
  loses, so held centre cores cannot be paid for with Balaban's large-field bounds. This is independent of the
  threshold `r0` and of the root suppression, which is used up after `O(A/(g_h² polylog))` steps.
* **The only way through that I see:** treat the neighbourhood of a held centre core as **small-field relative to a
  vortex background**. That means a Gaussian fluctuation theory with normalisation `O(1)` per site, not
  `log g^{-2}`, around the minimal-action configuration with −1 flux through the coarse plaquette (a thick vortex,
  twisted sector). This needs:
  * the constrained minimiser around that background (a `[15]` analogue);
  * propagator bounds around it (a `[13]` analogue);
  * a per-step cost `C_1` independent of `g`;
  * then the rate condition `b c_v log L > C_1` (P3 of `D-PIN.md`), which may or may not hold. `C_1` contains the
    fluctuation-determinant ratio vortex/no-vortex per step and could itself grow with `log L`.
  
  None of this exists in Balaban's papers or here. It is the quantitative form of the owner's reading: a held record
  must cost, per step of the transition, less than the flow releases.
* **Balanced stars at centres** (`NO-TRAP.md`) are a further case: `Vortex.lean` does not cover them, and excision may
  or may not remove them. Not decided.

## 5. Status

* F1 counting: **repair sketched** (section 3), with four named lemmas open.
* F1 persistent centre cores: **blocked**. The missing ingredient is a small-field theory around vortex backgrounds
  plus the rate condition (section 4). Not attempted; it is not routine and should not be started without the owner.
* F2, F3, F6: absorbed by the repair for released cores; open for held cores (section 4).
* F4, F5: still needed under the repair; fixable-looking, not done.
* Notes not edited to hide the error. Status lines added to `TRAP.md`, `S1-PROOF.md`, `M1-PLAN.md`.
