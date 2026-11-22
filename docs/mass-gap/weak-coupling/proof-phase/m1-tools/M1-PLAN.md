# M1: outline of the accompanying paper, and the estimate inventory (m1-tools, 2026-11-22)

> **Status (2026-11-22): the trapping design is broken by REVIEW-1 F1; current main line in section 0** (`../m1-review/REVIEW-1.md`): the root count here assumes one position per cell per scale, valid only for cores pinned at nested centres, while trapping traps every deep plaquette; records are then dense in physical units and the bounds are not uniform. Assessment and repair attempt: `F1-REPAIR.md`. The text below is left as it was.

## 0. Current status and main line (2026-11-22, after REVIEW-1; supersedes the status statements below)

**Decision on reflection positivity (coordinator, 2026-11-22).** M1 does **not** claim reflection positivity of
the blocked laws. The main assembly uses reflection positivity only as `LimitRP`, proved from the bare Wilson measure
(`rp_gaugeMeasure`). The block-law inputs (`BlockGapBddW`, `LawGapBddW`, `ObsTransferPhysTW`) are decay and transfer
statements, and the strong-coupling side (one-box route) uses no reflection positivity. The `rp_map` aim of
`TWIST.md` and the T2 check of `TRAP-CHECKS.md` are dropped as no longer required. The current blocking (global
decoder, `CLOSING.md`) is **not** reflection positive (`CLOSING.md` 4).

**The main line.**
1. **Blocking.**
   * Split each SU(2) bond into its adjoint SO(3) part and the Z2 layer `τ_p = sign tr U_p` (the exact
     Mack-Petkova/Tomboulis rewriting, `ROUTE-B.md` 1).
   * Close the bare Z2 layer once with the decoder: in each connected union of Balaban's scale-0 `M R_0`-cubes that
     contain a flip, take the maximum-weight packing of positive-gain closed sets, with ties absorbed, then a
     lexicographic order (`CLOSING.md`, `REVIEW3-RESPONSE.md` 5).
   * Block the Z2 layer by mod-2 Stokes.
   * Block the SO(3) part with Balaban's average, excising for one step the SO(3) plaquettes near the cut (threshold
     `r0 = c/L⁴`, F4), so that constrained variables stay below `r0` (E7.J, easy form).
2. **Law preservation:** the conditional step (`Exact.lean`) for any measurable blocking.
3. **Small fields:** Balaban's analysis. At scale 0, small field means SU(2)-regular (so `τ = +1`); from scale 1 on,
   it means SO(3)-regular, and `τ'` enters only through label factors (`REVIEW3-RESPONSE.md` 1, 4).
4. **Large fields** (deep cores, SO(3)-cut plaquettes and monopole loops, Bianchi halos, sheets during their window):
   ordinary Balaban large-field regions, renormalised after the delay and **released** into R-terms. Released effects
   are gauge invariant and local; their field dependence is of dimension 4 (no invariant vector in `so(3)`), summed by
   [III] (2.30)-(2.33) (`F1-REPAIR.md` 2-3, `BYPASS.md` 1).
5. **Persistent Z2 flux:** only closed remainders feed the coarse bit, through the coarse 1-skeleton; count
   `L^{(1 - 16b)k}`, converging (`CLOSING.md` 2). Thick-born sheets never enter `τ`; they are large-field regions
   during a window of about `(3/4) log g^{-2}/log L` steps and are then erased (`BYPASS.md` 1). Labels are carried as
   positive fixed-domain factors (`REVIEW3-RESPONSE.md` 4).
6. **Hand-over at `L_*`:** the law of `(V_K, τ_K)` in Balaban's form, and the `L_*` half of the ultraviolet transfer.
   The crossover `L_* → L₁` (P4) is not M1's (`HANDOVER.md`).

**Routes tried, and why they were set aside.**

| route | idea | outcome | note |
|---|---|---|---|
| deterministic Lemma D | every core dilutes | false: centre vortices persist under every covariant symmetric average (`Vortex.lean`) | `NOTE.md` 2.4 |
| random shifts (D-prob) | shifts dilute deep cores | shifts buy `≤ L^{-d}` per step against Balaban's per-step cost | `D-N.md` |
| pinning + Z2 labels + cut avoidance | hold cores at nested centres | cut avoidance NT′(b′) open; uniform capture false (slow balanced stars) | `D-PIN.md`, `NO-TRAP.md`, `NT-A.md`, `NT-B.md` |
| trapping at creation, records for ever | freeze every deep core, excise, pay root + maintenance | **fatal** (REVIEW-1 F1): records dense in physical units; F2 Bianchi halo | `TRAP.md`, `F1-REPAIR.md` |
| release + records only at nested centres | counting repaired | persistent centre cores cost polylog per step, more than the flow frees | `F1-REPAIR.md` 4 |
| route (b), SO(3) × Z2 split | store the centre bit on boundaries | central persistence removed; a thin sheet is an action maximum for SO(3) (the act at the tie) | `ROUTE-B.md` |
| act-region background | fluctuation theory around a thick vortex | no minimum at finite thickness (runaway); charged quartic zero mode | `MILESTONE-1.md` |
| bypass, labels by plain mod-2 Stokes | carry sheets as costly large fields | sheets close; open single flips on the 2-skeleton diverge (`b A_1 ≤ 0.94 < 2`) | `BYPASS.md` |
| **closing rule (current)** | only closed sheets feed the coarse bit | counting converges; not RP (dropped as not required) | `CLOSING.md` |

**What remains for M1, with claim levels** (everything else in the main line is Lean, paper or citation as listed in
the notes):

| item | content | level |
|---|---|---|
| R1 off-centre dilution (F5, in SO(3)) | contraction of localised moderate cores at every position (in-block parts cancel; only segments transmit) | **paper + Lean steps** (`OFFCENTRE.md`, `OffCentre.lean`): `θ = 5^d L^{1-d} + C(r0 + L² ε)`; sheets are not R1 (excision R3, growth R2) |
| R2 regular within the delay | every released region is regular within the delay, or is carried, paid by its own action | **paper + Lean step** in the repaired form (`R2-REPAIR.md`): attribution instead of a partition; footprint-weighted lifetime (`footprint_sum_le`); suppression from [16] (71) (read); E8 insertion a re-reading of [V] (1.80)-(1.85); the remainder route (`R2-REMAINDER.md`) compared and not taken: its rarity bound (a) closes, its splitting (b) needs a defect-decoupling lemma; **E8: no insertion needed**, [V] (1.80)-(1.81) already allow `K ≤ n0 - j + R_j` with `n0` the shrinking time (`R10-SCOPE.md` 1; `REGULAR.md` 0.4 misread it) |
| R3 filling near the cut (F4) | holes = twist-free envelopes of deep structures; filling = small-field Dirichlet problem; swallowed blocks filled globally (no per-block rule, RP dropped) | **paper** (`FILL.md`); the old hole (deep plaquettes only) was wrong: the data carried the flux |
| R4 fibre mass with excision (E7.J) | needed only at regular `W`; swallowed coarse bonds | **paper, explicit** (`FILL.md`, `SKETCH-STEPS.md` 1): ordinary bonds as `E7J.md`; swallowed bonds get an independent Haar value (fibre density 1). Design change: blocking with auxiliary randomness (`Interface/RandBlocking.lean` allows it) |
| R5 action lower bound (F6) | the bound behind [V] (1.76) | **read**: [16] (69)-(71), action in the four blocks of an irregular coarse plaquette `≥ ¼|V(∂p') - 1|²/g²`, given regularity (68) of the finer field; proof via [12] (50), (53), any dimension |
| R6 decoder locality | the decoder's output enters Balaban's `T`-operations as a function of their own variables | **paper** (`REVIEW3-RESPONSE.md` 5): local by definition, per component of the flip cubes of Balaban's scale-0 grid. The conflict-graph Peierls bound (`REVIEW2-RESPONSE.md` 1) is kept as a fidelity estimate. The merging rule and the global decoder's locality claim are withdrawn |
| R7 normalisation per real flip | `Z_{−P}/Z ≤ (C β^{3/2})^{|P|}` (R7′) | **citation**, exponent derived by a rank count (`REVIEW3-RESPONSE.md` 3); the Jensen route and `f(P) ≤ |P|/6` withdrawn (REVIEW-3 H6) |
| R8 release of acts and labels | dimension-4 coupling, summable | **paper** (`CLOSE-OUT.md` 2): no-linear-coupling lemma (gauge invariance and no invariant vector in `so(3)`); sum `ε_k² Σ_j e^{-p0(g_j)}` (needs `p0` growing faster than `log(k - j)`, i.e. `A0 > 1` if `p = 1`); labels no longer use it (fixed-domain factors, `REVIEW3-RESPONSE.md` 4) |
| R9 Balaban for the SO(3) layer | carry-over of [I]-[V] to the adjoint field | **citation** carry-over with the change table (`CLOSE-OUT.md` 5): small field means SU(2)-regular at scale 0 (`τ = +1`, N-1) and SO(3)-regular from scale 1 on; no centre; otherwise constants only |
| R10 hand-over (b) | the `L_*` half of the ultraviolet transfer, `L¹` form | **sketch** (`WRITEOUTS.md` 2): REVIEW-3 H4, the split must use the positive partition and the probability bound needs a scale-`K` normalisation; part 2 |
| R12 [16] (71) in 4D | the action lower bound behind [V] (1.76) in four dimensions | **paper**, written out from [12] (48)-(53) (`CLOSE-OUT.md` 1) |
| G2/H1 labels | labels in Balaban's form | **paper** for components with `δ_k |X| ≤ 1/4`; **citation-level** for the normalised-operation Mayer expansion and the carrying within the lifetime; **sketch** for the super-rare tail (`REVIEW3-RESPONSE.md` 4) |
| H3 one-step induction | `S1-CURRENT.md` written as the induction, with the order of constants | **outline** only; part 2 |
| N-2 density | the block-observable class is dense in the limit | **open**; part 2 (bears on the interface) |
| R11 interface | measurable blockings with noise (done, `Interface/RandBlocking.lean`); block state `(SO(3), closed Z2)` with gauge-invariant observables (no SU(2) encoding, REVIEW-2 G5) | formal refactor, outside M1's folders |
| ext | [I] Theorem 2 (running coupling, with `γ ≤ γ0(L)`) | external, unpublished |
| P4 | the crossover `L_* → L₁` | not M1's; open, the core |

F2 (Bianchi halo) and F3 (P2′) are absorbed: halos live in released large-field regions, and P2′ is not needed
because nothing is frozen. V1 with excision (`V1-EXCISION.md`, `V1-INPUTS.md`) is no longer on the main line: holes are
never inside small-field domains. The Lean modules `Twist.lean` (`rp_map`) and `CutAvoid.lean` are off the main line;
`Exact.lean`, `Dilution.lean`, `Vortex.lean`, `FibreMass.lean`, `Routine.lean`, `FluxTube.lean` and `Assembly.lean`
(as bookkeeping, REVIEW-1 F7) remain in use. **Verdict (corrected after REVIEW-3 and the REVIEW-2 follow-up, 2026-11-22).** The earlier verdict, "complete at
paper level", overstated what is written and is withdrawn. M1 is a complete programme. The counting, the decoder, the
labels' form, the small-field rule and the extended holes are repaired. Still to be written:
* **H3:** the one-step induction (`S1-CURRENT.md` is an outline). Part 2.
* **H4:** R10's split on the positive partition, with a scale-`K` normalisation (sketch). Part 2.
* **N-2:** density of the block-observable class in the limit (open; bears on the interface). Part 2.

Repaired in `REVIEW3-RESPONSE.md`:
* N-1 (paper);
* H2, the local decoder (paper);
* H1, labels as fixed-domain factors: paper for small components, citation-level extension, super-rare tail sketch;
* H5 (paper, one sketch step);
* H6 (citation, exponent derived).

As before:
* **external:** [I] Theorem 2 with its rate (0.31);
* **separate:** P4;
* **outside M1:** the interface changes.

What each part rests on:
* **Lean (machine-checked):** exactness of the conditional step, dilution and off-centre steps, slicing, Poincaré
  counting, local-modification identities, fibre densities, gauge fixing at a leaf, the flux-tube bound, the footprint
  sum, and the assembly as bookkeeping. Unchanged: 57 theorems in 12 modules, standard axioms.
* **Paper:**
  * R1, R2 (repaired), R3, R4, R12;
  * the closing rule and the count;
  * the local decoder;
  * N-1;
  * the labels' form for small components;
  * extended holes (with one sketch step).
* **Sketch:**
  * R10;
  * the footprint-weighted lifetime in [V] (1.80)-(1.85) (super-rare tails of R2 and of the labels);
  * "cap reached implies irregular `W`" (`FILL.md` 0.2).
* **Outline:** the induction (`S1-CURRENT.md`).
* **Citation:**
  * Balaban [I]-[V], [12]-[16] as stated;
  * R9 carry-over;
  * R7′;
  * the normalised-operation Mayer expansion of [V] (1.103) used for labels;
  * [13] (3.133)'s illegible exponents.

Parts A and B below are the pre-review plan, kept for the record.

M1 = Balaban's large-field operation R ([IV], [V]) redone so that the effective densities stay the **laws** of the
block fields. The owner (2026-11-22): M1 becomes **an accompanying paper to the main series** (which starts with GUID
v8), "rock solid". Part A is the paper's outline, section by section, with what each section proves and how
(**Lean** = machine-checked in `formal/ProofPhase/M1/`; **paper** = proved on paper in the notes of this folder;
**sketch** = argument written, gaps named; **citation** = Balaban, equation given; **numerical**; **open**). Part B is
the full inventory of estimates (rows referenced as S1, X1, …). The paper itself is not written yet.

## Part A. Paper outline

**Working title.** A law-preserving large-field step for four-dimensional SU(2) lattice gauge theory.

**Main theorem (target).** For the Wilson measure on a 4D torus at weak bare coupling, the laws of the successive
(twisted) block fields have Balaban's inductive form ([III] (2.18), [V] (1.104)) with the bounds of [III] Sect. 2,
uniformly in the number of steps, the lattice spacing and the volume, given the running-coupling input of [I]
Theorem 2. In words: Balaban's control of large fields, which in his papers holds for integrals, holds for the laws.

| § | content | results and their status | sources here |
|---|---|---|---|
| 1 | **Introduction.** Balaban's R keeps integrals, not laws ([IV] p. 200, [V] p. 378); why laws are needed (expectation values, the infrared input of the main series); the three new ingredients (conditional step, twisted blocking, rooted cores) | — | `../c5d-supplier/BALABAN-READING.md`, `../c6f-m1scope/ONE-STEP.md` |
| 2 | **Setting.** Lattices, Balaban's block average [I] (0.3)-(0.4), densities and large-field regions [III] Sect. 2, constants (with the retuning of §6) | citation | `NOTE.md` 1, `D-N.md` 1 |
| 3 | **The conditional step and its exactness.** `R̂`: resample on `Λ` in the fibre of the next field, ratio `N/D`; `T R̂ = T` term by term; branches (a)/(b); gauge-fixing removal exact inside `T` | **Lean** (`map_resample_eq`, `map_comp_resample_eq`, `sum_map_resample_eq`, `map_resample_rnDeriv_eq`); hypothesis H1 (fibre densities) and X2 open (routine, 2 pp.) | `NOTE.md` 3, `Exact.lean`; rows X1, X1.H1, X1.H2, X2 |
| 4 | **The twisted blocking.** Z2 label field plus smooth part; small-field identity with Balaban; covariance, symmetry, locality; link reflection positivity of every layer; exactness with labels | **Lean** (`Twist.lean`: `twistBlock_one`, `_pureGauge`, `_gauge`, `_sym`, `_local`, `rp_map`) + **paper** (that Balaban's average, the decimation and the creation/drop rules meet the hypotheses) | `TWIST.md` 1-3, `P0.md`; row P0 |
| 5 | **Core dilution and trapping.** (5.1) Star weights of Balaban's average, exact; moderate cores dilute by `L^{1-d}` per step (Lemma D-mod); off-centre cores are diluted to spread `< 0.1` in one step at `L = 13`. (5.2) Deep cores: vortex persistence for every covariant symmetric average (deterministic dilution is false); slow balanced stars (uniform capture fails). (5.3) **Deep cores are trapped**: after a fixed delay (0-2 steps) they are frozen as holes and **excised** from the block average (per-block canonical filling), carried as records; charged once at the root plus a summable maintenance cost (P2′). The cut is never met; no capture or cut-avoidance lemma is needed. (5.4, optional) For centre-valued cores, Z2 labels instead of excision; cut avoidance NT′ for the plain average | (5.1) **Lean** core + **paper** + **numerical**, constants `K, K'` open; (5.2) **Lean** + paper + **numerical**; (5.3) **paper** (`TRAP.md`), checks T1-T4 open (routine-looking); (5.4) NT′(a) **proved** (Lean cap half), Cap Lemma open, not on the critical path | `NOTE.md` 2, `D-PIN.md` 2, `TWIST.md`, `NO-TRAP.md`, `TRAP.md`, `NT-A.md`, `NT-B.md`; rows D-mod, D-vortex, TRAP, P0, NT′ |
| 6 | **The step under the block constraint.** Constrained minimiser for the conditional step's data, nested as sets (`[15]` Thm 1, Prop 9); background regularity; linear term (exact identity); quadratic form on `ker Q`; denominator and exact Wilson cancellation; normalisations; analytic extension; large-field factors (with the fibre-mass bound E7.J); entropy induction with Balaban's own delay and exponents (no retuning once deep cores are trapped); fundamental inequality; polymer gas and exponentiation | V1, X1.H2, E1, E2 **paper** (`S6-START.md`); E3 **paper** (`E3.md`, `POINCARE.md`; counting step **Lean**); E5, E6, E8, E9 **paper** carry-overs (`E5-E9.md`); E7 and E7.J **paper** (`E7J.md`; slicing step **Lean**); E4, E11-E13, V2 **citation** | rows V1, V2, E1-E13, E7.J; `S6-START.md`, `E3.md`, `E5-E9.md`, `E7J.md`, `POINCARE.md`, `V1-EXCISION.md` |
| 7 | **Rooted cores.** One root per pinned or trapped core; no suppression used twice; root suppression `exp(-A_min/g_h²)`; root once + maintenance summed (P2′) `≪` root; sum over roots `≤ exp(-A_min/(2g_k²))` | root bookkeeping **paper**; P4 **citation level**; P2′ **proof** given Balaban's bounds I1-I3 | `D-PIN.md` 3-4, `P2-PRIME.md`, `TRAP.md` 3; rows D-pin, TRAP, P2′, P4 |
| 8 | **The inductive form for laws; main theorem.** Assembly of §3-7 | **Lean** `m1_assembly` (`Assembly.lean`): under named hypotheses (fibre representation, `0 < D < ∞`, the definition of `T`, the bare form, and `stepEstimates` bundling §5-§7), the RG densities are the true laws at every scale and have the inductive form; `m1_laws`: the law half needs none of the estimates ; row by row: `m1_assembly_rows` with one named hypothesis per row; up to the stopping scale `m1_assembly_rows_upTo` (rows stated in `S1-ROWS.md`) of Part B and S1 as the combination ; the step itself on paper (`S1-PROOF.md`) | row S1; `Assembly.lean`, `S1-PROOF.md` |
| A | **Appendices.** A1 reading map of Balaban's papers (where each estimate sits); A2 numerics (star weights, star dynamics, twisted lattice tests) with scripts; A3 the excluded devices (random grid shifts, `D-N.md`) | **paper** + **numerical** | `NOTE.md` 1, `D-N.md`, scripts in this folder |

**What is solid now.** Exactness (§3), the algebra and positivity of the twisted blocking (§4) and the logical assembly (§8) are
machine-checked;
moderate-core dilution (§5.1) has its elementary core in Lean and its weights checked exactly; the deterministic
obstruction (§5.2) is a Lean theorem; the root bookkeeping (§7) and the constant retuning (§6) are proved on paper.

**What is not.** The S1 bookkeeping write-up and the routine rows; the Cap Lemma is open but no longer needed; uniform capture is
not true as stated (slow balanced stars). P2′ (§7) rests on Balaban's bounds I1-I3 used as black boxes. The
constrained estimates of §6 (about 25 pages, routine) and the assembly (§8) are unwritten; the running-coupling input
([I] Theorem 2) is external and unpublished.

## Part B. Estimate inventory (every estimate the paper needs)

| # | estimate | Balaban source | M1 version | status | size |
|---|---|---|---|---|---|
| S1 | inductive form for laws: (2.18) with R-terms allowed to depend on `U_k` through `M(U_k)` on `Λ`; block-axial gauge on `Λ`; the `W` partition `1 = χ(W reg) + χ^c(W reg)` and branch (a) | [III] (2.17)-(2.42); [IV] (0.2)-(0.6) | restate for laws; branch (a) terms are current large fields of `V_{k+1}` | **paper** (`S1-PROOF.md`: one step in order, `Form_{k+1}` item by item, record weights, constants in order); logical form **Lean** (`m1_assembly_rows_upTo`), record gas **Lean** (`record_gas_le`) | done |
| X1 | **exactness** `T R̂ = T`, term by term | [IV] (1.99), (1.102) (where Balaban loses it) | `map_resample_eq`, `map_comp_resample_eq`, `sum_map_resample_eq`, `map_resample_rnDeriv_eq` | **Lean** (given H1, H2 below) | done |
| X1.H1 | `N`, `D` are the δ-integrals against fibre Haar measure (fibre representation) | [I] (0.13); [12] | block map a submersion on regular configurations | **Lean** existence (`fibre_rep_of_map_le`, from the E7.J bound) + paper (`ROUTINE-ROWS.md` 1) | done |
| X1.H2 | `0 < D(W) < ∞` for regular `W` | [V] (1.10)-(1.11) | the constrained minimiser lies in the fibre and in the support of `ŵ` | **paper** given V1 (`S6-START.md` 3); quantitative bound in E3 | 0 |
| X2 | gauge-fixing removal (L3) exact inside `T` | [V] p. 378; [I] (0.14)-(0.16) | Faddeev-Popov with block-axial gauge, Jacobian 1 | **Lean** one leaf (`lintegral_gauge_leaf`) + paper induction over the forest (`ROUTINE-ROWS.md` 2) | done |
| P1 | preliminary integrations | [IV] (1.10)-(1.99), pp. 177-193 | unchanged; all operations exact (read in full, `NOTE.md` 1.1) | **citation** (confirmed) | 0 |
| P2 | restriction `χ_{k,Λ}` and extension of regular `V_out` into `Λ` | [IV] (1.74)-(1.75) | unchanged | citation | 0 |
| V1 | constrained minimiser `V̂_Λ(W, V_out)` for the two-scale determining set: existence, uniqueness, regularity `O(B5 M^5)(ε_k + ε_{k+1})`, analyticity in `(W, V_out)` | [IV] Prop. 1, (1.77)-(1.80); [V] (1.12)-(1.13), (1.38)-(1.45); `[15]` Sects. D, E, G | fixed point on `P_0 ∩ ker Q_{k+1}` | **paper**: `[15]` Theorem 1 and Proposition 9 (`S6-START.md` 2); with excision checked section by section (`V1-EXCISION.md`); its two inputs proved (`V1-INPUTS.md`: Lemma FR, finite-rank local modifications, identity and decay step **Lean**; Lemma LP, positivity), using only Balaban's own citations (`[5]` Thms 3.12, 3.13; `[6]` Thm 2) | 2 |
| V2 | background `U_0(W)` regular on all scales in `Λ`; gauge; `χ''_k = 1` | [IV] (1.80)-(1.98) | same with block-axial gauge | **paper** (carry-over of [IV] (1.77)-(1.98), `ROUTINE-ROWS.md` 3) | done |
| D-mod | **Lemma D, moderate cores**: spread of the core's image shrinks by `θ = L^{1-d} + K r0 + K' ε` per step | new; analogue of [V] (1.31), (1.47) | `NOTE.md` 2.2-2.3 | **paper** + **Lean** (`balaban_star_dilution`, `spread_iterate_quadratic`, `norm_wsum_sub_wsum_le`); exact weights checked by `star_weights.py`; constants explicit: `K = 8`, `K' = 8dL²` (`ROUTINE-ROWS.md` 4) | done |
| D-vortex | deterministic Lemma D for all cores is **false** (centre vortex persists under every covariant symmetric average) | new; [I] (0.4), [IV] (1.2)-(1.9) | `NOTE.md` 2.4 | **Lean** (`vortex_persists`, `su2NegOne`) + paper (Balaban's average has the hypotheses) | done |
| D-shift | shift-averaged blocking leaves every blocked law unchanged | new | `NOTE.md` 2.5 | paper (exact, short); **not needed** after D-N | 0 |
| D-prob | **Lemma D-prob**: under i.i.d. uniform shifts a deep core stays deep for `n` steps with probability `≤ p_stayⁿ`, `p_stay = O(L^{1-d})` | new | `NOTE.md` 2.5; missing: cone bound `f(z) ≤ C |z - y'|^{1-d}` on the path fraction, multi-site bookkeeping | **ruled out as a device** (`D-N.md` 2: shifts buy `≤ L^{-d}` per step, Balaban charges `exp(O(1) log g^{-2}(MR)^d)` per step); the estimate itself not needed | 0 |
| D-N | constants: D-prob needs `N ≳ p0(g)/((d-1) log L)`, i.e. `ν ≥ p0`; compatible with `½ν ≤ p0 - p1 - 1` iff `p0 ≥ 2p1 + 2`; recent-region entropy then at equal powers (`A0 > 4 log L` times a constant) | [IV] p. 198; [V] p. 363, (1.80)-(1.85), p. 389 | `D-N.md` | answered (paper, `D-N.md`); the retuning is **not needed** once deep cores are trapped (`E5-E9.md` 0) | done |
| D-pin | **deep cores pinned at nested block centres**: root rule (one root per core, suppression charged once, core carried as a Z2 label plus a frozen hole) | new | `D-PIN.md`, `P0.md`, `TWIST.md`, `P2-PRIME.md` | **SURVIVES WITH LEMMAS**: P0 (written), NT′ (cut avoidance, open), P2′ (proof given Balaban bounds I1-I3), P4 (citation level); root bookkeeping paper | see P-rows |
| TRAP | **trapping of deep cores**: still deep after a fixed delay `N_t ∈ {0, 1, 2}` ⇒ frozen hole, excised from the block average (per-block canonical filling), record kept; root once + maintenance (P2′) | new (the owner's proposal, `../../PREP.md`) | `TRAP.md` | **paper** (`TRAP.md`, `TRAP-CHECKS.md`, `V1-INPUTS.md`): delay `N_t = 0`, threshold `r0 ≤ c/L²`, holes closer than `R_sep(d, L)` merged; accounting by covering numbers, any hole size (`S1-ROWS.md` F3) | 1 |
| P0 | **twisted blocking**: Z2 label field + smooth part blocked by (0.4) + straight-path decimation of labels; creation at isolated centre patterns, drop on contradiction | new; [I] (0.4), p. 254 | `TWIST.md`, `P0.md`; `Twist.lean`; `lattice_twist.py`, `twist_dynamics.py` | definition, small-field identity, covariance, symmetry, locality, link RP: **Lean + paper**; no trapping: **numerical** (`d = 2, 3` multi-level; `d = 4` one-site `L = 13` and full lattice `L = 3`, 2 steps); proof open | optional since TRAP (labels for centre-valued cores) |
| P2′ | **subscale hole decoupling**: `|Δ_k| ≤ C[ρ_k^{d-2}(1 + p0²) + ρ_k^{(d-2)/2} p0 (1 + a^{1/2}/g_h)]`, `ρ_k = D0 L^{-(k-h)}`; summed `≪ a/g_h²` | new; [13], [II], `[15]` Thm 1 and (9)-(10); [I] (1.18), [II] (2.41), [III] (2.31), (2.42) | `P2-PRIME.md` v2 | **paper** given I1-I3 as Balaban states them; written up (`P2-PRIME.md` 5, v3: records of any size, covering numbers, Lemma F) | done |
| NT′ | **cut avoidance**: (a) every star has a sign pattern with corrected relative angles `≤ θ_root < π`; (b′) at most `N_cut` near-cut steps over a pinned core's orbit. Replaces uniform no trapping, which fails (slow balanced stars) | new | `NO-TRAP.md`, `NT-A.md`, `NT-B.md` | (a) **proved**: `θ_root = 2 arccos s_8 = 168.7°` (union bound on `S³`, paper; cap half **Lean** `CutAvoid.lean`); (b′) **reduced** to the one-step **Cap Lemma** (the star map keeps every cap of radius `< 90°`; then `N_cut = 0`), open, numerically supported (300-step orbits, fixed-cap test up to 89°) | 0 (off the critical path since TRAP) |
| P3 | rate condition `A_min b log L > C_1`, `b = 22/(6π²) ≈ 0.37` (not needed if P2′ holds) | [III] (2.42), [I] Thm 2 | `D-PIN.md` 4(b) | open (constants) | 1 |
| P4 | root suppression of a deep core `exp(-A_min/g_h²)`, `A_min = c0 r0²` | `[15]` Thm 1; [V] p. 380 | `D-PIN.md` 4 | **paper** (`ROUTINE-ROWS.md` 5): `A_min = c_P r0²/(C_d² L⁴)`; needs `γ ≤ γ0(L)` (`S1-ROWS.md` F4) | done |
| E1 | linear term: `J_0 = Q*_{k+1} λ` on `Λ`; its core contribution `≤ g_k^{-2} ε_{k+1} θ^{n_mod} r0 ≪ 1` | [V] (1.2)-(1.6), (1.28)-(1.29), p. 363 | Lagrange-multiplier identity, D-mod | **paper**: exact identity (critical point on `Q δA' = 0`, `S6-START.md` 3); no core term (frozen hole) | 0.5 |
| E2 | quadratic form positivity on `ker Q_{k+1}` | [V] (1.7)-(1.9) | Poincare bound `O(L²)` (better) | **paper**: restriction of a positive form (`S6-START.md` 3) | 0.5 |
| E3 | denominator `D_X(W) = exp[-g_k^{-2}A(ζ0, U_0(W)) - Î + Ê_k(Λ)]`, `|Î| ≤ O(1)M^5 + O(log g_k^{-2})` per constrained bond; Wilson term cancels | [V] (1.10)-(1.11), (1.30)-(1.37) | W-dependent, analytic, non-zero on regular `W` | **paper** (`E3.md`; Poincaré (1.8) for the block-axial gauge in `POINCARE.md`, counting step **Lean** `sum_sq_le_of_paths`) | 1 |
| E4 | localization of the `W`-dependence | [V] (1.14)-(1.69), pp. 359-376 (pp. 364-373 now read) | enters only through `U_0(W)` and shell shifts | **paper** (carry-over of [V] (1.12)-(1.69), `ROUTINE-ROWS.md` 6) | done |
| E5 | `T̂'_k(X)` and matched normalisations `E_k(X)`, `(-½ d(g) log g^{-2} + log σ0)|B0 \ T0|` | [V] (1.70)-(1.71) | numerator and denominator constrain the same bonds | **paper** carry-over (`E5-E9.md` 1) | 1 |
| E6 | analytic extension `|T'(X,(U,J))F| ≤ T'(X)1 e^{sup|σ|} sup|F|` and lower bound | [V] (1.73)-(1.75) | needs (D1): D-mod for moderate cores; deep cores: D-pin | **paper** carry-over (`E5-E9.md` 1) | 1 |
| E7 | large-field factors under δ-constraints (pointwise; group integrals with δ bounded by the Jacobian `O(1)^{|Λ|}`) | [V] (1.76)-(1.79) | uniform in regular `W` | **paper** (`E5-E9.md`, `E7J.md`) | 1 |
| E7.J | **fibre mass**: the density of the blocked Haar measure is `≤ C(L)` per coarse bond, uniformly in the next field | new | `E5-E9.md` 2: each coarse bond owns its face-crossing bonds; bounded density of sums of independent terms | **paper** (`E7J.md`) given trapping at creation (`N_t = 0`) and `r0 ≤ c/L²`: owned face bonds, uniform submersion; slicing step **Lean** (`map_prod_le_of_slices`); the cut-flag route compared in `E7J.md` 5 (equivalent once complete; thick vortices need the `c/L²` threshold) | done |
| E8 | entropy induction `κ_j(Z)` | [V] (1.80)-(1.88) | extra `O(1)` per step from the `W` partition and Jacobians | **paper** carry-over; Balaban's `N = R_j` and exponents stand once deep cores are trapped (`E5-E9.md` 1) | 1 |
| E9 | fundamental inequality `sup_{W reg} N_X(W)/D_X(W) ≤ exp(-2(1+β0)^{-1} p0(g_k))` | [V] (1.89) | changed constants | **paper** given E5-E8 (`E5-E9.md`) | 0.5 |
| E10 | fresh factor in branch (a) (D2) | ONE-STEP 2.3 | moderate cores: D-mod + the regularity theorem (Theorem 1 of `[15]` as ONE-STEP cites it; to be checked against `[15]`); deep cores at nested centres: **false** (D-vortex), shifts do not help (D-N) | moderate: paper (NOTE 2.3); deep: root rule (D-pin) | 1 |
| E11 | polymer gas, vacancy-1, activities `|F| ≤ c1 exp(-(1+β)κ d(X'))` | [V] (1.90)-(1.97) | activities depend on `W` on `Λ_j`: local on the same domains | **citation** (checked, `ROUTINE-ROWS.md` 7) | done |
| E12 | exponentiation, new R-terms `|R''(X)| ≤ exp(-p0) exp(-κ d_k(X))`, new action | [V] (1.98)-(1.101), p. 389 | unchanged | **citation** (checked, `ROUTINE-ROWS.md` 7) | done |
| E13 | final form `R̂ρ_k` in the form [III] (2.18); next `T` | [V] (1.102)-(1.104); [III] Sect. 3 | unchanged; `T R̂ρ_k` is the law (X1) | **citation** (checked; normalisation of the conditional step, `ROUTINE-ROWS.md` 7) | done |
| ext | running coupling stays below `γ` | [I] Theorem 2 (unpublished) | independent of M1 | open (external) | — |

## Totals

* **Lean (52 theorems, 9 modules, standard axioms; all listed in `axioms.log`):** exactness (`Exact.lean`), moderate dilution core (`Dilution.lean`),
  vortex persistence (`Vortex.lean`), twisted blocking and `rp_map` (`Twist.lean`), cut avoidance at the root
  (`CutAvoid.lean`), the assembly `m1_assembly`, row by row `m1_assembly_rows` and up to the stopping scale
  `m1_assembly_rows_upTo` (`Assembly.lean`), fibre-mass slicing and Poincaré counting (`FibreMass.lean`), the
  resolvent identity and decay through a set (`LocalMod.lean`), fibre densities, gauge fixing at a leaf and the record gas
  (`Routine.lean`).
* **Paper:** every row of Part B except the citations below: D-N, root bookkeeping, link RP of the twisted and excised
  blockings, P2′ (written up), P4, NT′(a), TRAP (accounting, T1-T4), V1 (with excision and its inputs), V2, D-mod
  (explicit constants), X1.H1, X1.H2, X2, E1-E9, E7.J, the block-axial Poincaré bound; S1 and every row stated
  precisely (`S1-ROWS.md`); the S1 bookkeeping (`S1-PROOF.md`).
* **Citation (checked):** P1, P2, E11-E13; Balaban's I1-I3 (used by P2′) and `[5]` Theorems 3.12, 3.13, `[6]` Theorem
  2's linear bounds (used by V1), all as Balaban states them.
* **Numerical (adversarially checked):** the `d = 4`, `L = 13` off-centre step, local contraction, long orbits, the
  fixed-cap test.
* **Open:** the write-up of the paper (the owner decides when it starts). Everything M1 rests on outside itself:
  `EXTERNAL.md`.
* **Off the critical path:** the Cap Lemma, the Z2 labels, the constant retuning of `D-N.md`.
* **False as first stated:** deterministic Lemma D (vortex), uniform no trapping (slow balanced stars).
* **External:** [I] Theorem 2 (with `γ ≤ γ0(L)`, `S1-ROWS.md` F4).

## Order of work (recommended)

1. The write-up of the paper, when the owner starts it.
