# M1 referee review 2 (adversarial), 2026-11-22

Scope: the current main line of M1 (`../m1-tools/M1-PLAN.md` section 0) and the notes it rests on: CLOSING, DECODER-LOCAL,
ROUTE-B, F1-REPAIR, BYPASS (item 1), OFFCENTRE, REGULAR, R2-REPAIR, R2-REMAINDER (skimmed), FILL, SKETCH-STEPS,
CLOSE-OUT, R10-SCOPE, HANDOVER, EXTERNAL; the older notes the main line still cites (S1-ROWS, S1-PROOF, E5-E9, E7J,
ROUTINE-ROWS, V1-INPUTS, status lines only for TRAP, TWIST, NOTE); the Lean files `ProofPhase/M1/*.lean`,
`ProofPhase/Interface/{MeasBlocking,RandBlocking,SpectralUpgrade}.lean`, the consumers `V3/W1Route.lean`
(`ObsTransferPhysTW`), `V4/Gap.lean` (`BlockGapBddW`, `LawGapBddW`); `m1-r11/NOTE.md`; and spot checks of Balaban's
text (local PDFs, text layer extracted with `pdftotext`): [V] pp. 383-386 ((1.79)-(1.83)), [III] Sect. 1-2 (definition of
`R_0`, `R_j`, `p0`). REVIEW-1 was read only after the findings below were formed. Nothing was built or re-run.

## Verdict

The redesign does remove REVIEW-1's fatal error: nothing is frozen or recorded for ever any more, the only objects that
survive to the stopping scale (closed Z2 remainders on the coarse 1-skeleton) are counted in physical units correctly
(`16 b = 1.49 > 1`), and everything else is released after a window shorter than Balaban's delay. I found no new FATAL
error with high confidence. But M1 is not at the level the plan claims ("every row has an argument"): the one-step
induction for laws (S1) has not been rewritten for the current design at all (the notes it cites are the broken trapping
versions), the surviving Z2 labels have no consistent place in Balaban's inductive form (they are excluded from
small-field domains by R9, but cannot be Balaban large-field regions either), the decoder's locality estimate is wrong
as written, and the hand-over is not delivered: no hypothesis of the formal assembly is supplied, the SU(2) encoding of
the block state is not gauge covariant, and the reflection-positivity upgrade that is supposed to replace the uniform
transfer bound does not work on the finite tori of the interface as argued. I would rate M1 as "plausible programme
with the main counting fixed", not as an argument modulo [I] Theorem 2 and P4.

## Findings, most severe first

### G1. There is no one-step induction (S1) for the current main line

* **Location.** `M1-PLAN.md` 0 ("Main theorem, final status": "every row above has an argument"; "Paper, written out:
  ... the counting"); `S1-PROOF.md`, `S1-ROWS.md`, `E5-E9.md`, `E7J.md`, `ROUTINE-ROWS.md` 7; `Assembly.lean`
  (`M1RowStatements`).
* **Claim.** The rows R1-R12 plus Balaban's papers give the main theorem; the S1 bookkeeping is "paper (`S1-PROOF.md`)".
* **Failure.** `S1-PROOF.md` carries the status line "broken by REVIEW-1 F1" and was not redone. `S1-ROWS.md` (26
  mentions of records/trapping), `E5-E9.md` ("with deep cores trapped", "trapped records are not regions of the
  induction", E6 through "per-block fillings"), `E7J.md` ("given trapping at creation, `N_t = 0`, `r0 <= c/L^2`") and
  `ROUTINE-ROWS.md` 7 (records merged per `R_sep`) are all written for the trapping design. The current design changes
  the state space (SO(3) field plus a closed Z2 layer), the regular set (R9: `tau = +1`), the block map (global decoder at
  step 0, excision with global hole filling, randomised swallowed bonds), and the large-field bookkeeping (release,
  attribution, labels). None of the E-rows has been re-checked against these changes; R10's sketch (`CLOSE-OUT.md` 3)
  even cites `S1-ROWS.md` 1 for "the bounds of the inductive form". In Lean, `M1RowStatements` still has the rows
  `Dmod`, `TRAP`, `P2prime`, `P4`, which are off the main line, and no rows for the decoder, the Z2 layer, the release
  or R1-R12.
* **What is missing.** A statement of `Form_k` for the law of `(V_k, tau_k)` (including how `tau_k` and the randomised
  bonds enter the densities), and the one-step bookkeeping in the order of `S1-PROOF.md` 2 for the new map. This is
  where G2, G3 and G6 below have to be resolved.
* **Severity:** GAP (major; the main theorem's induction is unwritten). **Confidence:** high.

### G2. The persistent Z2 labels fit neither half of Balaban's inductive form

* **Location.** `CLOSING.md` 2 (count of closed remainders); `CLOSE-OUT.md` 5 (R9 table, first row: small-field domains
  require `tau = +1`) versus `CLOSE-OUT.md` 2 ("Labels ... enter the coarse density through a local factor"); `M1-PLAN.md`
  0 items 4-5; [V] (1.76), (1.80)-(1.83) (checked in the PDF).
* **Claim.** Closed remainders on the coarse 1-skeleton feed the coarse bit; their count per scale-`k` cell is
  `<~ e^{-16/g_k^2} L^{(1-16b)k}`, which converges, so they are harmless.
* **Failure.** The count is right (G-checks below), but it is the count of a *rare object*, not a bound in Balaban's form.
  A label created at the bare scale on a bond of the scale-`k` skeleton persists for `k` steps (up to `K`, which grows
  without bound as the lattice spacing goes to zero). By R9 a region with `tau_k != +1` is never small-field, so the
  conditional step never renormalises it (`Reg` requires a regular next field) and it stays a large-field region for its
  whole life. But it cannot be one of Balaban's large-field regions:
  * it has no large-field factor: [V] (1.76) gets `exp(-p0)` from an irregular coarse plaquette through [16] (71); at a
    label the SO(3) field is smooth (the bubble's SO(3) core sat at the cut and was excised and filled at step 0), so
    there is no action lower bound at any scale `>= 1`;
  * it outlives Balaban's control: [V] (1.80) lets `exp(-kappa_j(Z))` control `K <= n0 - j + R_j` steps "under the
    assumption that no large fields are created", after which the region must satisfy (i), (ii) and be renormalised;
    a label persists for `k - j >> R_j` steps;
  * carried anyway, it costs `O(1) M^d R^{d+1} = polylog(g^{-2})` per step ([V] p. 380), against a one-time suppression
    `e^{-16/g_0^2}` whose growth is only `1.49 log L` per step. Per cell the bound becomes
    `e^{-16/g_K^2} exp(K (polylog - 0.49 log L))`, which diverges. This is `F1-REPAIR.md` 4's own computation for held
    centre cores, applied to the labels.
  
  `CLOSE-OUT.md` 2 instead treats labels as local factors in the coarse density, which would make them small-field with
  a discrete index, contradicting R9 two sections later. Neither treatment is written.
* **Likely repair.** Drop `tau = +1` from the small-field definition at scales `>= 1` where the SO(3) field is regular,
  and carry each label as a polymer with activity `<= L^k e^{-16/g_0^2}` and an analytic, local, gauge-invariant
  dependence on `V_k` (R8's lemma then gives the dimension-4 coupling). This needs a lemma: the conditional law of `V_k`
  near a label is Balaban's small-field law times a local analytic factor. Not routine, but no obstruction is visible.
* **Severity:** GAP (severe as written: under R9 the bound diverges). **Confidence:** medium-high that the notes do not
  handle it; medium that the repair works.

### G3. R6: the decoder's locality estimate is false as written

* **Location.** `DECODER-LOCAL.md` 0, 4, 6.1 ("a cluster of `n` flips ... has probability at most `C^n e^{-(beta-c)n}`";
  "`P(output at q depends on flips at distance >= r) <= sum_{n >= r/C} C^n e^{-(beta-c)n}`"; enlargement of Balaban's
  large-field regions by radius `<= 2|K|` "costs at most a constant factor").
* **Claim.** The merging rule (merge `K, K'` when `dist <= 4(|K| + |K'|)`) gives small clusters with exponential tails.
* **Failure.**
  * The shape count is not `C^n`. Links may have length up to `4n`, so a cluster of `n` flips built by adding one flip at
    a time at distance `~4m` to a group of size `m` has about `prod_m m^4 ~ (n!)^4` placements; the sum over `n` of
    `(n!)^4 e^{-beta n}` diverges.
  * Worse, the rule percolates. A compact group of `m` flips merges with every flip within distance `4m`; its
    `4m`-neighbourhood holds about `rho (4m)^4` flips at flip density `rho`, which exceeds `m` once
    `m >~ rho^{-1/3}`. Such a group grows without bound with probability close to 1, and seeds of that size occur
    with positive density per site. So in infinite volume, or on a torus whose side grows at fixed lattice spacing, the
    whole box is one cluster with probability tending to 1. (At fixed physical volume and `a -> 0` the seeds disappear,
    because `rho = e^{-beta_0}` falls like a power of `a`; but M1 claims uniformity in the volume.)
  * The deterministic lemma of section 3 is correct (the Steiner/MST step should be done with the doubling walk, since
    set distances are not a metric, but the inequality holds), so the decoder *is* the product of per-cluster decoders.
    Only the probabilistic use of these clusters fails.
* **Likely repair.** Use the components of `sigma*` and chains of overlapping positive-gain closed components
  (`2|tau ∩ S| - |S| > 0`) instead of the merging clusters. In a minimal chain each plaquette lies in at most two
  members, so the union `U` is connected with `|tau ∩ U| >= |U|/4`, and the Peierls count `C^u e^{-beta u/4}` gives
  exponential locality of the decoder output. Section 4's enlargement of Balaban's regions has to be redone with these
  sets.
* **Severity:** GAP (proof wrong; conclusion very likely true). **Confidence:** high on the error.

### G4. The hand-over does not deliver the assembly's inputs; the RP upgrade is mis-argued on tori

* **Location.** `R10-SCOPE.md` 0.4-0.5, 2, 3 (both caveats); `CLOSE-OUT.md` 3; `HANDOVER.md` 2; `SKETCH-STEPS.md` 2;
  `Interface/SpectralUpgrade.lean`; `V3/W1Route.lean` 156-175; `Interface/RandBlocking.lean` 160-175.
* **Claim.** M1 delivers at `L_*` the inputs a formal mass-gap assembly needs; the uniform-over-measurable form of
  `ObsTransferPhysTW` is "not needed" because RP of the bare measure upgrades dense-class decay with per-observable
  constants to the uniform gap, "level by level", "the constants may depend on `k` and `F`".
* **Failures.**
  1. **On a finite torus the dense-class hypothesis has no content.** With time extent `N`, correlations are
     `tr(T^{N-n} F T^n G)/tr T^N` and only `n <= N/2` is available. A bound `C_F e^{-m n}` for finitely many `n` with an
     `F`-dependent (and level- and volume-dependent) `C_F` holds for every `F` trivially. The log-convexity argument of
     `SpectralUpgrade.lean` needs `<G, T^n G>` for **all** `n`, i.e. the infinite-time limit at fixed spatial size.
     `R10-SCOPE.md` 3 (second caveat: "dense-class decay for `n <= N/2` forces `lambda_1/lambda_0 <= e^{-m a_k}`") is
     false as stated; it becomes true only with `C_F` uniform in `N` and a family of tori with fixed spatial size and
     `N -> infinity`. The interface's tori (`T.side k j`) are cubic, so no such family exists there.
  2. **The upgrade acts on full correlations; M1 gives only the conditional half.** R10 (CLOSE-OUT 3 (i), (ii)) is
     conditional decoupling given `(V_K, tau_K)`. The dense-class decay of full correlations needs P4 and the infrared
     input with per-observable constants; `ObsTransferPhysTW` conditions on the block field at `L_1`, not `L_*`. No
     statement anywhere (paper or Lean) splits the transfer into an `L_*` half and a P4 half.
  3. **Nothing is formal.** `ObsTransferPhysTW_dense` is not defined; `SpectralUpgrade.lean` is an abstract Hilbert-space
     lemma (correct, see below) with no transfer matrix built from `rp_gaugeMeasure` and no link to `TorusDecayLoc`.
     So M1 currently supplies none of `BlockGapBddW`, `LawGapBddW`, `ObsTransferPhysTW` or their `Rand*`/`Meas*`
     versions, not even the `L_*` half as a named statement.
  4. **R10's sketch overstates pointwise decoupling.** "`E[F | V_K]` depends on `V_K` near `A` up to `e^{-kappa D}`"
     cannot hold pointwise: if the conditioning `V_K` itself carries a large-field region joining `A` to far away,
     Balaban's large-field terms (upper bounds only, no lower bounds) give no decay in the ratio
     `rho^{(t)}_K / rho_K`. Only the `L^1` form (which is what the interface asks for) is plausible, via the probability
     of such regions. Also the insertion `e^{tF}` with complex `t` puts the conditional step outside `Exact.lean`
     (ENNReal densities; see F7 below).
* **Severity:** GAP. **Confidence:** high for 1 and 3, medium-high for 2 and 4.

### G5. The SU(2) encoding of the block state is not gauge covariant (hand-over, R11)

* **Location.** `HANDOVER.md` 0.3 ("lift each SO(3) bond canonically and multiply by `z_c`, with `dz = tau` fixed by a Z2
  axial gauge ... Gauge-invariant local observables of the encoding are local functions of `(V, tau)`");
  `m1-r11/NOTE.md` ("Open": encoding not done); `MeasBlocking.viaState`.
* **Failure.** With canonical lifts `U^_b` and `dz = tau`, the encoded plaquette is `tau_p * (product of canonical lifts)`,
  whose sign is `tau_p xi_p(V)`, where `xi_p` is the lift-branch sign of the four bonds. `xi_p` depends on the SO(3)
  gauge representative, not only on the gauge class. The block law of `V_K` is invariant under SO(3) gauge
  transformations, under which each bond is spread over all of SO(3), so `xi_p = -1` at a positive fraction of
  plaquettes even where `V_K` is small-field, and the sign of every encoded fundamental Wilson loop is randomised. The
  encoded law is not SU(2)-gauge invariant and does not look like a weak-coupling SU(2) law, which is what P4 and the
  one-box route are meant to receive. The covariant choice `dz = tau xi(V)` has a solution only where `d xi = eta(V_K)`
  vanishes, i.e. not where `V_K` has coarse SO(3) monopoles (large-field regions, present at positive density in large
  volume). So "an SU(2) encoding exists" is true only in the trivial measurable sense; a physically meaningful one is
  not given.
* **Consequence.** Either the P4/one-box side is restated for the SO(3) x Z2 state (gauge-invariant observables only),
  or an encoding is defined after gauge fixing with its locality analysed. This affects the claim that M1 hands over
  "the law of `(V_K, tau_K)`" in a form the assembly consumes.
* **Severity:** GAP. **Confidence:** medium.

### G6. R3: the hole construction does not cover the extended holes the main line relies on

* **Location.** `FILL.md` 0.2-0.3, 2, 3; `OFFCENTRE.md` 0.5; `BYPASS.md` 1; `R2-REPAIR.md` 4.
* **Claim.** At regular `W` every deep structure is localised in a ball of radius `<= C L`; the twist-free envelope is
  capped at radius `C L`; the filling is a Dirichlet problem with data within `C r0 diam(N)` of a pure gauge,
  `diam(N) <= C L`.
* **Failure.** In SO(3) a thin centre-flux sheet is deep (rotations up to `pi` across it) but invisible to holonomies
  (`Ad(-1) = 1`); its block image is regular. So "deep structures at regular `W` are localised" is false for exactly the
  sheets that OFFCENTRE 0.5 and R2-REPAIR 4 send to "excision and filling" in their thin phase. For such a hole (a
  thickened 2-surface of large area), the growth cap "radius `C L`" is ambiguous (layers versus extent), the axial-gauge
  bound `C r0 diam(N)` is not small, and the uniqueness estimate is stated only for `diam <= C L`. The rule for several
  components of `H` (each grows by a layer while any one is not twist-free?) is also not specified.
* **Likely repair.** Cap the number of growth layers, not the extent; do the filling with local gauges in the thin
  direction (the Dirichlet gap is set by the thickness). Plausible, but not written, and E7.J (R4) has to be re-checked
  for long holes.
* **Severity:** GAP (fixable-looking). **Confidence:** medium.

### F7. Lean: assembly still bookkeeping, now stale; positivity of terms still unstated

* **Location.** `Assembly.lean`; `Exact.lean`; `M1-PLAN.md` 0 ("Lean (machine-checked): ... the record gas; ... the
  assembly as bookkeeping").
* **Facts.** REVIEW-1 F7 (i)-(iv) all still apply. The rows are now also the wrong rows (see G1). (iv) is aggravated:
  `map_resample_eq` is for `ENNReal` densities, while R10 applies the conditional step to `e^{tF} mu` with complex `t`,
  and Balaban's history terms after the Mayer expansion are signed. The extension by linearity is easy (the reference
  kernel `w` stays positive, only `N` becomes signed or complex), but it is not stated.
* **Severity:** FIXABLE. **Confidence:** high.

### N1. R7: the normalisation is not `O(1)` per flip in general

* **Location.** `CLOSE-OUT.md` 4.
* The Chebyshev-plus-Jensen reduction is correct as an inequality, but `<1 - tr U_p/2>_{-S} <= c/beta` fails when removing
  `S` frees bonds (all plaquettes of a bond in `S`): then those bonds are Haar and the bound is `1`. For the sets the
  counts need (thin closed surfaces, small clusters) no bond is freed and the factor is at most polynomial in `beta`
  per flip, which the power margins (`0.49` per step) absorb. State it as `poly(beta)^{|tau|}` and restrict to sets that
  free no bond, or handle dense sets by their own Peierls count. **NIT/FIXABLE**, confidence medium.

### N2. Twist sectors are not defined uniformly in the volume

* **Location.** `DECODER-LOCAL.md` 6.3-6.4.
* `w2` of the block field is defined only when the SO(3) field is regular on a whole non-contractible plane. Balaban's
  large-field regions have positive density per volume, so in a large torus every plane meets one, and the
  decomposition "the law is the sum over twist sectors" is not available uniformly in the volume. Nothing quantitative
  uses it (for the periodic SU(2) model the total twist is trivial anyway), so it should be dropped rather than repaired.
  **NIT**, confidence medium-high.

### N3. Smaller points

* **NIT, `EXTERNAL.md` row 1:** still omits the rate of [I] (0.31), which CLOSING's convergence now uses quantitatively
  (margin `16 b' > 1` needs the effective rate within about 33 % of one loop; with the adverse tie-break, 11 %).
  REVIEW-1 F8, still open.
* **NIT, `M1-PLAN.md` 0:** lists "blockings with auxiliary randomness" as a needed interface change, but
  `Interface/RandBlocking.lean` and `MeasBlocking.lean` already implement it (proved, standard axioms per
  `m1-r11/axioms.log`). The plan is out of date there.
* **NIT, `SpectralUpgrade.lean` header:** cites "`m1-r11/NOTE.md`, section R12", which does not exist; "R12" also names
  the [16] (71) row in `M1-PLAN.md` 0.
* **NIT, `REGULAR.md` 0.2 / `EXTERNAL.md`:** "the exponent of `R_j` is unreadable". The extracted text layer of [III]
  (Sect. 1, definition of `R_0`) reads as `R_0 >= (log g_0^{-2})^r` with `r >= 2`, and [V] (1.80)-(1.81) uses `R_j` as a
  number of steps (`N = R_j`, "at most `R_j` further steps"). This supports `n_1 ~ 0.4 log g^{-2} <= R_j` (R2-REPAIR,
  R10-SCOPE 1); worth pinning.
* **NIT, `DECODER-LOCAL.md` 4:** "diameter `<= C n^2`" and "`<= C n` along any minimal chain" are in tension; moot after G3.
* **NIT, `FILL.md` 3:** "unique modulo gauge" needs a measurable gauge selection when the hole contains block centres
  (Balaban's average is covariant there); trivial to supply.

## Status of the REVIEW-1 findings

| REVIEW-1 | status | comment |
|---|---|---|
| F1 records dense in physical units | **resolved** by redesign | No records; released regions counted like Balaban's own. The surviving objects (closed labels) converge in physical units, but their place in the inductive form is open (G2): a milder form of the same "carried for ever" problem, not a relabelling of the counting error. |
| F2 Bianchi halo | **resolved** | Nothing is frozen; halos lie inside released regions; FILL's twist-free envelope answers "the data carry the flux". Residual: extended holes (G6). |
| F3 P2' Lemma E | **resolved by removal**, partly **relabelled** | P2' is off the line. The same "frozen region of arbitrary content" problem reappeared in R10 for measurable observables (SKETCH-STEPS 2) and was sidestepped by the analytic class plus the RP upgrade, whose torus form is not established (G4). |
| F4 filling / E7.J | **mostly resolved** | `r0 = c/L^4`; twist-free envelopes; randomised swallowed bonds give fibre density 1 (explicit, and the randomised interface exists in Lean). Residual: G6; E7.J itself (`E7J.md`) is still written for the trapping set-up (G1). |
| F5 off-centre D-mod | **resolved** (paper) | OFFCENTRE's structural argument checks: the `B(y)`-part of (0.4) has the same law for incoming and outgoing bonds, so its first-order effect is a coarse gauge transformation; segments give `L^{1-d}` per bond. Lean steps are elementary, as stated. |
| F6 P4 citation | **resolved** | P4 off the line; [16] (69)-(71) read and re-derived in `d = 4` (CLOSE-OUT 1; the power count `L^{(4-d)j}` checks). |
| F7 Lean assembly | **still open** | Presentation partly fixed ("bookkeeping"), but rows are stale (TRAP, Dmod, P2', P4) and positivity of terms is unstated (F7 above). |
| F8 smaller points | **mostly moot / open** | S1-PROOF (branch labels, constants list) is broken and not redone (G1); EXTERNAL row 1 rate still missing (N3); T2 moot (RP dropped). |

## What I checked and found sound

* `Exact.lean`: correct; the conditional step preserves the law of any measurable conditioning variable, including the
  decoder output, the swallowed set and the noise (on the product space). Law preservation with the global decoder,
  excision with global filling and the randomised bonds holds: each is a measurable function of (configuration, noise),
  with the tie locus `tr U_p = 0` of Haar measure zero.
* `Interface/RandBlocking.lean`: the `Rand*` statements are the originals with the integrals over `ym ⊗ P` and
  conditioning on the joint space; the deterministic case reduces by `Iff` lemmas. The torus-decay port uses only the
  map and `cov_transfer`, as its docstring says (read, not rebuilt).
* `Interface/SpectralUpgrade.lean`: the abstract lemma is correct and needs no spectral theorem (log-convexity of
  `<G, T^n G>` for positive symmetric `T`, closure, invariant subspace). The problem is its application (G4).
* The ROUTE-B rewriting (`tau_p = sign tr U_p`, `d tau = eta(Ad U)`, the Tomboulis weight) and BYPASS item 2 (single
  flips on the 2-skeleton diverge, `b A_1 <= 0.94 < 2`), which is why the closing rule is needed.
* CLOSING 2: the per-component majority inequality `|tau ∩ sigma_a| > |sigma_a|/2` (removing a closed component, ties to
  smaller `|sigma|`); smallest closed remainder 6 plaquettes, hence 4 real flips; `b = 0.0929` is the one-loop SU(2)
  rate of `g^{-2}` with `beta = 4/g^2` (i.e. `d beta/d log(1/a) = 0.372`); `16 b = 1.49`, `12 b = 1.11`; positions on
  the 1-skeleton `d L^k` per scale-`k` cell. Monopole-loop filling area `>= l/4` (each plaquette lies in 4 cubes).
* DECODER-LOCAL 3, deterministic part (with the walk fix), and 6.2 (a wrapping closed cochain has `>= N_min^2`
  plaquettes; Peierls on the component).
* R8's no-linear-coupling lemma, and the summability `eps_k^2 sum_j e^{-p0(g_j)}`: Balaban's
  `p0(g) = A0 (log g^{-2})^{p0}` with integer `p0 >= 1` and `A0` large ([III] Sect. 1), so the sum converges.
* R10-SCOPE 1 against [V] (1.80)-(1.83) in the PDF: `K <= n0 - j + R_j`, the geometric sizes via [I] (6.31), and "no
  large fields created" referring to `S(Z) \ Z`; a sheet inside `S^{n-j}(Z)` is in that case. E8 needs no insertion,
  given that the few-cube phase fits in `R_j` (N3).
* R2-REPAIR's physical-unit counts (extended regions born with `n_s >= L^{k-s}/2`, suppression linear in birth size) and
  BYPASS 1's window count (`L^{4 window} = g^{-6}` against `e^{-A_1^2 p0^2}`).
* The randomised swallowed-bond rule (SKETCH-STEPS 1): fibre density exactly 1, and the random bonds are twist-free in
  4D, so the next excision fills them.

## What I could not check, and why

* [I]-[V] line by line, in particular R9's claim that the SO(3) carry-over changes "constants only" in [13], [15],
  [IV], [V]; the E-row carry-overs for the new map (they do not exist yet, G1).
* [V] (1.76) in full (whether a region renormalised after `R_j` steps that is still irregular gets a new `exp(-p0)`
  without finer regularity); the OCR of the displayed bounds is poor.
* The scripts and logs (`route_b_cores.py`, `single_flip.py`, `offcentre_cancel.py` and others) were not re-run; no
  main-line claim I rely on depends only on them.
* The Lean files were read, not rebuilt; `axioms.log` and `m1-r11/axioms.log` were taken as given.
* MILESTONE-1 and R2-REMAINDER were only skimmed (off the main line).
