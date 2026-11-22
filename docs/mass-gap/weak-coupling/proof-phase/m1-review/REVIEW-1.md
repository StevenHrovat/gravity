# M1 referee review 1 (adversarial), 2026-11-22

Scope: the M1 notes in `../m1-tools/` (M1-PLAN, NOTE, TWIST, P0, TRAP, TRAP-CHECKS, P2-PRIME, D-PIN, D-N, S6-START, E3,
POINCARE, E5-E9, E7J, V1-EXCISION, V1-INPUTS, S1-ROWS, S1-PROOF, EXTERNAL, ROUTINE-ROWS, NO-TRAP), the Lean files
`formal/ProofPhase/M1/*.lean`, and spot checks of Balaban's text in the local PDFs ([I] CMP 109, [III] CMP 119,
[V] CMP 122 p. 355, `[15]` CMP 102). The material was taken as final (S1-PROOF.md and EXTERNAL.md included).

## Verdict

The exactness half of M1 is sound: the conditional resampling step preserves the law of the conditioning variable
(the Lean proof is correct and the argument is elementary), and records, labels and excision can all be put into the
conditioning variable without breaking it. The estimate half is not sound as written, and the problem sits in the
part that replaced the earlier open lemmas: trapping deep cores at creation and carrying them as records for ever.
The most serious problem (F1) is a counting error: the root sum is taken over a bounded number of positions per scale,
a count that was valid for cores pinned at nested block centres (D-PIN) but not for trapping, where every deep plaquette
anywhere becomes a permanent record. With the true count, the number of records per coarse cube grows without bound as
the lattice spacing goes to zero (the root suppression gains only a power of the lattice spacing, the number of
positions grows like its inverse fourth power), so records cannot stay separated, the merging rule swallows the
small-field region, and the bounds are not uniform in the number of steps. Independently (F2), a frozen hole whose
deep flux does not close inside the hole forces, by the lattice Bianchi identity, a plaquette of size at least r0/5
next to the hole for ever, so the record never meets the stated condition for the decoupled phase and its carrying
cost, summed over the scales it lives through, exceeds its own root suppression. I could not find a repair of F1 that
keeps "records carried for ever"; the design probably has to forget (integrate out) old records, and then their
cumulative effect per coarse cube has to be bounded, which is not done anywhere.

## Findings, most severe first

### F1. Records are not dilute in physical units; the root sum counts the wrong positions

* **Location.** `TRAP.md` 3 (last table row, "per cell, `O(R0^d)` positions per scale"), inherited from `D-PIN.md` 3
  ("Multiplicity": `O(R0^d)` positions per scale) and 4(a); `S1-PROOF.md` 4 ("The record gas", "per site");
  `S1-ROWS.md` 1 (records pairwise `R_sep`-separated at scale `k`, F2); `V1-INPUTS.md` FR-multi.
* **Claim.** Summed over roots, records cost at most `C exp(-A_min/(2 g_k^2))` per scale-`k` cell; the record gas
  changes the free energy "per site" by at most `exp(-A_min/(2g^2))`.
* **Failure.** D-PIN counted only cores pinned at nested block centres (a core that persists must sit at a coarse site
  of every scale, one per cell). Under TRAP every plaquette of every block field `V_h` at angle `>= r0` starts a record
  at once (`N_t = 0`), at any position, and the record is never integrated or forgotten (`S1-ROWS.md` (F-d): contents
  are conditioning variables; P2-PRIME: maintenance "for ever"). A scale-`k` cell contains `L^{d(k-h)}` scale-`h` sites.
  With the per-site weight `exp(-A/g_h^2)` and asymptotic freedom `g_h^{-2} - g_k^{-2} ~ b (k-h) log L` (the rate in
  [I] (0.31); `D-N.md` 3 uses `b ~ 0.09` for SU(2)), the expected number of records per scale-`k` cell is about
  `exp(-A/g_k^2) * sum_{j>=0} L^{(d - bA) j}`. This converges only if `b A > d`, i.e. `A > ~43` for `d = 4`. M1's `A`
  is `A_min = c_P r0^2/(C_d^2 L^4)` with `r0 <= c/L^2`, of order `L^{-8}` (for `L = 13`, `c = 1/32`: about `4e-15` times `c_P`);
  even the largest possible single-plaquette action is far below 43. So for fixed `g_k = gamma` at the stopping scale,
  the expected number of records per coarse cell grows like `L^{d k}` (up to a factor `exp(-A/gamma^2)`) as the number
  `k` of steps from the bare lattice grows, i.e. as the lattice spacing goes to zero. This is just the fact that
  lattice-scale fluctuations above a fixed angle are suppressed only by a power of the lattice spacing.
* **Consequences.** (i) The separation rule (holes `>= R_sep` apart at scale `k`, needed for FR-multi, hence for V1,
  LP and P2') fails for typical configurations once records are dense; the merging rule then produces holes spanning
  whole cubes, which are not subscale and must sit in the large-field region `Z_k`. The small-field region disappears
  at scales far from the bare lattice. (ii) The "mixture form: smooth block field + a rare set of records" (`TRAP.md`
  0.5) is false in physical units. (iii) `M1-PLAN.md` lists P3 (the rate condition `A_min b log L > C_1`) as "not needed
  if P2' holds"; P2' bounds one record's maintenance and says nothing about how many records there are, so the rate
  condition (in the stronger form `b A > d`) comes back, and it is false for every admissible threshold.
* **Repair?** Not evident. Forgetting a record once decoupled turns its frozen content into a local term at later
  scales; summing those effects over root scales gives roughly `sum_j L^{(d - bA) j} * |effect at age j|`, and with
  P2''s decay `rho^{d-2} = L^{-2j}` this still diverges in `d = 4`. Balaban avoids the issue because his large-field
  regions are renormalised away after the delay, not carried. A repair has to make old deep cores disappear into
  Balaban's machinery (or into perturbation theory) rather than persist as labels.
* **Severity:** FATAL for the main theorem as stated (uniform in the number of steps and the lattice spacing), with
  trapping as designed. **Confidence:** high for the counting; medium that no cheap repair exists.

### F2. A frozen hole never becomes "decoupled": lattice Bianchi identity

* **Location.** `P2-PRIME.md` 5 (decoupled phase: "`rho_k <= 1` and the neighbourhood `eps_k`-regular, which D-mod
  reaches after `n_mod` steps"); `S1-ROWS.md` (F-a) and F5; `V1-INPUTS.md` Lemma LP ("a plaquette next to a hole that is
  not eps-small puts its neighbourhood into the large-field region"); `V1-EXCISION.md` 1 (gradients of `deltaA` are
  `O(eps)`); `TRAP-CHECKS.md` T1, T4 (data "regular, all plaquettes within eps").
* **Claim.** After `log_L D0 + n_mod` steps a record's neighbourhood is `eps_k`-regular; the record then lies in a
  small-field domain and costs only the summable P2' maintenance.
* **Failure.** Since v3 the hole is only the connected component of plaquettes at angle `>= r0`, not the whole
  non-regular region (P2-PRIME v1 section 3 had the whole non-regular region, exactly so that the hole boundary is
  regular; v3 dropped this). For any 3-cube, the ordered product of its six face holonomies (suitably transported) is
  the identity, for every configuration. Take an isolated deep plaquette `p` (angle `theta >= r0`, so `H` = its four
  bonds) and a 3-cube containing it: the other five faces all contain bonds outside `H`, and their angles sum to at
  least `theta`, whatever the outside bonds are. So some plaquette next to the frozen hole has angle `>= r0/5` in
  every configuration and every background, for ever. The same holds wherever the deep set's flux does not close
  inside the frozen plaquettes, i.e. for generic deep cores (a smooth lump whose peak exceeds `r0`). D-mod cannot help:
  it acts on block fields, while these plaquettes involve the frozen root-scale content. F5's justification ("regular
  because Lambda is a small-field domain") is a non sequitur: the small-field test (2.17) is made on backgrounds built
  from the excised block field `V_k`, which never sees the frozen content.
* **Consequence.** By the notes' own rules such a record stays in `Z_k` (carrying phase) for its whole life. Carrying
  costs Balaban's per-cube charge `O(1) M^d R^{d+1}` per step ([V] p. 380, checked in the PDF; used the same way in
  `D-N.md` 2). From root scale `s` to the stopping scale there are up to about `g_s^{-2}/(b log L)` steps, so the
  carrying cost is about `polylog(g_s^{-2}) * g_s^{-2}/(b log L)`, which exceeds the root suppression `A_min n/g_s^2` as
  `g_s -> 0` (the polylog grows, `A_min` is fixed). Hence `w_r <= exp(-a_r/(2 g_s^2))` (F-f) is not proved and is false
  for this accounting.
* **Repair?** Two directions, neither written: (a) return to the v1 hole (the whole non-`eps`-regular component), then
  re-do the accounting with the frozen moderate halo (action `>= p0^2` per moderate plaquette against carrying costs
  per covering cube; holes may then be large), and re-check that freezing moderate fields does not conflict with D-mod;
  or (b) allow a decoupled record with an `O(r0)` boundary layer, which needs LP (it seems to tolerate `O(r0)` given
  `r0 <= c/L^2`), FR (`||V|| <= C(d,L)`), `[15]`'s data condition (7) (needs `r0` below `[15]`'s `alpha_1(d,L)`, a
  constant condition not in the list of S1-PROOF 5), and Balaban's analyticity domains [III] (2.34)-(2.39) near the hole
  (unclear). F1 remains in either case.
* **Severity:** GAP (severe; as written it breaks the record bound). **Confidence:** high for the Bianchi obstruction;
  medium for the size of the carrying cost (it depends on how a subscale record in `Z` is charged, which the notes
  only state as "polylog per cube").

### F3. P2' Lemma E: the perturbation is not small where it is used, and input I1 is mis-cited

* **Location.** `P2-PRIME.md` 2, Lemmas B, D, E; 5 (v3); `EXTERNAL.md` rows 13, 15.
* **Claim.** The hole changes Balaban's local terms by `C[rho^{d-2} + rho^{(d-2)/2}(p0 + a^{1/2}/g_h)]`, by Cauchy
  estimates, "the perturbation is small compared with the analyticity radii".
* **Failure.** (i) At the start of the decoupled phase (`rho ~ 1`) the claimed change is of order
  `p0 a^{1/2}/g_h >> 1` (S1-PROOF: `(C n)^{1/2}/g_s`). A perturbation that moves the local terms by more than `O(1)` is
  not inside the analyticity domain on which Balaban's bounds [I] (1.18), [III] (2.31), (2.42) hold, so Cauchy
  estimates do not apply; the cross term with the frozen mismatch `m_0` (of root size, not small-field size) is exactly
  the part that is large. S1-PROOF moves the maintenance into `w_r`, which fixes where it is booked but not the
  validity of the expansion that produces it. (ii) Lemma B needs the fine-scale smoothness of the linear response
  `A -> R_k A` (`|grad R_k A| <= C ||A|| L^{-2(k-h)}`). It cites `[15]` (9)-(10), which (checked in the PDF) bound the
  background minimiser on cubes, not the linear response to a fluctuation. The relevant statement is `[15]` (46)
  (`[13]` Theorem 3.12 as quoted), whose gradient bound carries `L^{j/2}` rather than `L^{j}` (as EXTERNAL row 15 itself
  transcribes it), i.e. only half the smoothness gain Lemma B uses. The resulting bound may still be summable, but it
  is not the one stated.
* **Severity:** GAP. **Confidence:** medium (scaling conventions of `[15]` (46) are hard to read in the scan).

### F4. Filling (T1/T4) and the fibre-mass bound E7.J assume small-field data that do not occur next to holes

* **Location.** `TRAP-CHECKS.md` T1, T4; `E7J.md` 2(b), (d); `S1-ROWS.md` TRAP (b).
* **Claim.** The per-block filling is unique modulo gauge and analytic because the data on `B \ H` are `eps`-regular;
  its plaquettes are `O(eps D0^{d/2})`; hence all loops of the average stay within 1/2 of the identity.
* **Failure.** By F2 the data next to a fresh hole always contain plaquettes of size `~ r0/5`, not `eps`. With data of
  size `r0` the T1 argument gives filled plaquettes up to `C r0 |H cap B|^{1/2} ~ C r0 L^{d/2} = C c` for `r0 = c/L^2`,
  `d = 4`. Uniqueness needs this below the Poincare constant of the hole with Dirichlet data (order `L^{-2}`), and E7.J
  needs loops of up to `C_d L^2` filled plaquettes within 1/2: both require `r0 <= c/L^4`, not `c/L^2`. Without
  uniqueness, measurability needs a selection and T2 (reflection positivity, which used uniqueness to get covariance)
  fails at the non-unique configurations. Also, E7.J only treats subscale holes ("all but `O(D0^{d-1})` face bonds
  qualify"); for a fresh, non-subscale hole in `Z` (where E7.J is also needed, `E7J.md` 5 point 2) a coarse bond whose
  face lies inside the hole has no owned free bond, and its value is a deterministic function of the data, so the
  fibre has no bounded density. Those coarse bonds must be removed from the state and the constraint; the notes say
  "bonds outside the holes" but never reconcile this with the claim that excised block fields above the root scale
  have no holes.
* **Repair:** probably `r0 <= c/L^4` (changing `A_min` to order `L^{-12}`, harmless once F1 is solved) or a maximum
  principle type bound for the filling, plus an explicit rule for swallowed coarse bonds.
* **Severity:** GAP (fixable). **Confidence:** medium-high.

### F5. D-mod: the "from then on each is a centre case" step is wrong

* **Location.** `NOTE.md` 2.3 ("Location"); `NO-TRAP.md` 1; `S1-ROWS.md` row Dmod; `ROUTINE-ROWS.md` 4.
* **Claim.** After one off-centre step a moderate core sits on the stars of coarse sites, and from then on Lemma D-mod
  (block-centre contraction `L^{1-d}`) applies.
* **Failure.** In Balaban's geometry the next coarse lattice consists of block centres, so a site of `T^(m+1)` is a site
  of `T^(m+2)` only for one site in `L^d`. A generic moderate core is off-centre at every step. The off-centre
  contraction is supported only numerically (`offcentre_L13.py`: path fraction `<= 0.125`, spread `<= 0.099` after one
  step for deep cores); no proof of an off-centre contraction factor (linear weights plus the BCH corrections) is
  given. The row Dmod states `s_{k+1} <= theta s_k` for every moderate core, which is only proved at block centres.
  Also, D-mod is a statement about localised star perturbations; extended moderate fields grow by `L^2` per step and
  are handled (correctly, I think) by trapping, but the notes never say so.
* **Severity:** GAP (likely fixable: the off-centre linear weights are explicit path fractions and the nonlinear
  estimate of ROUTINE-ROWS 4 should carry over). **Confidence:** high that the step is unproved.

### F6. P4 rests on a lower bound attributed to `[15]` Theorem 1, which does not state one

* **Location.** `ROUTINE-ROWS.md` 5(b); `EXTERNAL.md` row 14; `S1-PROOF.md` 4.
* **Claim.** "`A >= c sum_p |U(dp) - 1|^2` (`[15]` Theorem 1, the lower bound of the action by the block field's
  plaquettes)"; with threshold `r1` instead of `eps_k` the large-field factor becomes `exp(-c r1^2/g_k^2)`.
* **Check.** `[15]` Theorem 1 (read in the PDF) gives existence, uniqueness and regularity (9)-(10) of the minimal orbit,
  and only for data satisfying the smallness condition (7); it states no lower bound of the action by block
  plaquettes, and it does not apply to the large-field data P4 is about. [V] p. 380 obtains the `chi^c(P_j)` factor
  "using Theorem 1 [15] and (71) [16]"; the lower bound is presumably [16] (71), which is not at hand and is not listed
  in EXTERNAL for P4. In addition, the same fine plaquettes pay Balaban's own large-field factor for the region and
  the root suppression; S1-PROOF does not split the action explicitly (easy, since `r1 >> eps_k`, but "no suppression
  used twice" should be shown, not asserted).
* **Severity:** GAP (citation; likely fixable once [16] is read). **Confidence:** medium.

### F7. Lean: the assembly is a tautology presented as a structural result

* **Location.** `Assembly.lean` (`m1_assembly`, `m1_assembly_rows`, `m1_assembly_rows_upTo`); `M1-PLAN.md` "What is
  solid now"; `S1-PROOF.md` 0.1.
* **Facts.** The Lean statements are correct and use only standard axioms, but: (i) every row in `M1RowStatements` is
  an uninterpreted `Prop`, and `assemble` assumes `rows -> Form k -> Form (k+1)`, so `m1_assembly_rows_upTo` is
  induction on `k` and nothing else; the rows do not constrain anything (one could set every row to `True` and put all
  content in `assemble`). (ii) `m1_laws` follows from `nextDensity`, which defines `rho (k+1)` as the density of the
  pushforward; with `Reg k = empty` (no resampling at all) every hypothesis is satisfiable and the conclusion holds, so
  the "law half" is exactness of one resampling plus a definition. (iii) `M1Data` has one conditioning map `phi k` per
  scale, while the notes resample term by term with term-dependent `Lambda`, `phi`, `N`, `D` (`sum_map_resample_eq`
  exists but is not used in the assembly). (iv) Densities are `ENNReal`, so each resampled term must be non-negative;
  that Balaban's history terms are non-negative (real effective actions inside an exponential, positive `T`
  operations) is plausible but nowhere stated; it would fail if the step were applied after the Mayer expansion, whose
  activities are signed.
* **What is misstated.** "The logical structure of M1 is machine-checked", "the only things left to prove are the named
  hypotheses", and "laws at every k, no estimate needed" overstate the content: `fibreN`, `D_ne_zero` at scales beyond
  `K` rest on V1 and E7.J, which are only argued for small coupling.
* **Severity:** FIXABLE (presentation; the paper should present `Exact.lean` as the machine-checked core and the
  assembly as bookkeeping). **Confidence:** high.

### F8. Smaller points

* **NIT, `S1-PROOF.md` 2 step 4:** "branch (a) for regular `W`, branch (b) left as it is" reverses the labels used in
  NOTE.md 3 and Exact.lean (branch (b) = regular, renormalised; branch (a) = irregular, left as it is).
* **NIT, `EXTERNAL.md` row 1:** M1 uses not only `g_k <= gamma` but also the rate of [I] (0.31) (asymptotic freedom, in
  the root sums of TRAP/D-PIN and in F1/F2 above); the row should list it. [I] Theorem 2 as printed: for `gamma` small
  and a small target `g` there is a bare coupling with all `g_k` in `(0, gamma]`, `g_K = g`, and the bounds (0.31);
  proof deferred to a separate paper. Choosing `gamma <= gamma0(L)` after `L` matches it.
* **NIT, constants (`S1-PROOF.md` 5):** missing conditions: `r0` below `[15]`'s data smallness `alpha_1(d, L)` near
  holes (F2b), `r1 >> eps_k` (P4 (b) needs a margin, not just `A_min^{1/2} >= gamma p0(gamma)`), and `n_mod` (about
  `1.44 log g^{-2}` with `theta <= 1/2`) `<=` Balaban's delay `N = R_j`. None is circular; all can be added.
* **NIT, `S1-ROWS.md` F3:** `N_k(H) <= 3^d(n L^{-(k-s)} + 1)` drops the factor 2 of Lemma F.
* **FIXABLE, `TRAP-CHECKS.md` T2:** covariance of the filling under face reflections was derived from uniqueness (T1);
  for a translation-invariant per-block rule, covariance under face reflections needs invariance under the block's
  own centre reflections, which fails at configurations with mirror-image minimisers unless a symmetric selection is
  given. Only matters outside the uniqueness regime (F4).
* **NIT, scope of the main theorem:** the laws controlled are those of the twisted/excised block field together with
  the records, not of Balaban's block field. That is legitimate, but "Balaban's control of large fields holds for the
  laws" in the introduction should say which block field.

## Could not check

* `[13]` (= `[5]` of `[15]`) and `[16]` are not available locally; rows 15, 16, 20 of EXTERNAL and the lower bound in F6
  were checked only against Balaban's quotations.
* The OCR of [III] (2.34)-(2.39) (the analyticity spaces) is unreadable; whether an `O(r0)` boundary layer near a hole
  fits these spaces (F2 repair (b)) was not decided.
* V1-EXCISION's section-by-section check of `[15]` and the carry-overs E4, V2, E11-E13 were read for logic, not re-done
  line by line against Balaban.
* Numerical scripts and logs were not re-run (no critical-path claim depends on them except the off-centre step, F5).

## Checked and found sound

* `Exact.lean`: `map_resample_eq` and its corollaries are correct and prove what NOTE.md 3 says; the step preserves the
  joint law of the conditioning variable, so records, labels, frozen contents and merging decisions can all be put in
  `phi` (they are deterministic measurable functions of the next field and the outside field). The blocking with
  trapping, merging and excision is a deterministic function of the bare field (given a measurable selection for the
  filling, see F4).
* `Routine.lean`, `FibreMass.lean`, `LocalMod.lean`, `Dilution.lean`, `Vortex.lean`, `CutAvoid.lean`: statements match
  the notes and are elementary; no hidden hypotheses beyond those named (Dilution's `spread_iterate_quadratic` takes the
  nonlinear step bound as a hypothesis, as the notes say).
* E7.J's structure (owned face bonds, slicing, Jacobian `L^{1-d}` per owned bond) is right for configurations with all
  plaquettes below `c/L^2` and holes away from the chosen bonds; the owned-bond claim checks against [I] (0.4).
* The vortex persistence theorem and its use (deterministic dilution is false for covariant symmetric averages).
* D-N.md's use of [V] p. 380 (per-cube cost `O(1) log g^{-2} |Z_j| <= O(1) M^d R^{d+1}` per step): confirmed in the PDF.
  This is also what makes F1 and F2 serious.
* The order of constants in S1-PROOF 5 is not circular as listed (missing items in F8).
* Lemma FR (resolvent identity, compression, decay through a finite set) and Lemma F (covering numbers) are correct.
* The record gas inequality `sum_{R subset P} prod w <= exp(sum w)` is correct; the issue (F1) is the size of `sum w`
  per coarse cell, not the inequality.
