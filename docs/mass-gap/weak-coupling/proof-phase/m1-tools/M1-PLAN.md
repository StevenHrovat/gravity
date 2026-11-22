# M1: outline of the accompanying paper, and the estimate inventory (m1-tools, 2026-11-22)

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
| 6 | **The step under the block constraint.** Constrained minimiser for the two-scale determining set (`[15]` Thm 1), background regularity, linear term via `J_0 = Q*λ`, quadratic form on `ker Q`, denominator, normalisations, analytic extension, large-field factors, entropy induction with retuned exponents (`p0 > (2d+6) r`, `(p0+(2d+6)r)/2 < p1 < p0`; the [IV] p. 198 condition removed), fundamental inequality, polymer gas and exponentiation | V1 reduced to `[15]` Theorem 1 (**paper**, `S6-START.md`: the conditional step's data are nested as sets); X1.H2 and E2 follow; E1 becomes an exact identity; **citation** for the unchanged parts; **open (routine)** for E3, E5-E9 (about 20 pp.); `D-N.md` 1 (**paper**) for the constants | rows V1, V2, E1-E13, D-N; `S6-START.md` |
| 7 | **Rooted cores.** One root per pinned or trapped core; no suppression used twice; root suppression `exp(-A_min/g_h²)`; root once + maintenance summed (P2′) `≪` root; sum over roots `≤ exp(-A_min/(2g_k²))` | root bookkeeping **paper**; P4 **citation level**; P2′ **proof** given Balaban's bounds I1-I3 | `D-PIN.md` 3-4, `P2-PRIME.md`, `TRAP.md` 3; rows D-pin, TRAP, P2′, P4 |
| 8 | **The inductive form for laws; main theorem.** Assembly of §3-7 into [III] (2.18)-form for the laws | **open** (5 pp.); one Lean assembly theorem with the open estimates as named hypotheses would make the logical structure machine-checked (recommended) | row S1 |
| A | **Appendices.** A1 reading map of Balaban's papers (where each estimate sits); A2 numerics (star weights, star dynamics, twisted lattice tests) with scripts; A3 the excluded devices (random grid shifts, `D-N.md`) | **paper** + **numerical** | `NOTE.md` 1, `D-N.md`, scripts in this folder |

**What is solid now.** Exactness (§3) and the algebra and positivity of the twisted blocking (§4) are machine-checked;
moderate-core dilution (§5.1) has its elementary core in Lean and its weights checked exactly; the deterministic
obstruction (§5.2) is a Lean theorem; the root bookkeeping (§7) and the constant retuning (§6) are proved on paper.

**What is not.** The trapping checks T1-T4 (§5.3) are open (paper, routine-looking); the Cap Lemma is open but no longer needed; uniform capture is
not true as stated (slow balanced stars). P2′ (§7) rests on Balaban's bounds I1-I3 used as black boxes. The
constrained estimates of §6 (about 25 pages, routine) and the assembly (§8) are unwritten; the running-coupling input
([I] Theorem 2) is external and unpublished.

## Part B. Estimate inventory (every estimate the paper needs)

| # | estimate | Balaban source | M1 version | status | size |
|---|---|---|---|---|---|
| S1 | inductive form for laws: (2.18) with R-terms allowed to depend on `U_k` through `M(U_k)` on `Λ`; block-axial gauge on `Λ`; the `W` partition `1 = χ(W reg) + χ^c(W reg)` and branch (a) | [III] (2.17)-(2.42); [IV] (0.2)-(0.6) | restate for laws; branch (a) terms are current large fields of `V_{k+1}` | open (routine) | 5 |
| X1 | **exactness** `T R̂ = T`, term by term | [IV] (1.99), (1.102) (where Balaban loses it) | `map_resample_eq`, `map_comp_resample_eq`, `sum_map_resample_eq`, `map_resample_rnDeriv_eq` | **Lean** (given H1, H2 below) | done |
| X1.H1 | `N`, `D` are the δ-integrals against fibre Haar measure (fibre representation) | [I] (0.13); [12] | block map a submersion on regular configurations | open (routine) | 1 |
| X1.H2 | `0 < D(W) < ∞` for regular `W` | [V] (1.10)-(1.11) | the constrained minimiser lies in the fibre and in the support of `ŵ` | **paper** given V1 (`S6-START.md` 3); quantitative bound in E3 | 0 |
| X2 | gauge-fixing removal (L3) exact inside `T` | [V] p. 378; [I] (0.14)-(0.16) | Faddeev-Popov with block-axial gauge, Jacobian 1 | open (routine) | 1 |
| P1 | preliminary integrations | [IV] (1.10)-(1.99), pp. 177-193 | unchanged; all operations exact (read in full, `NOTE.md` 1.1) | **citation** (confirmed) | 0 |
| P2 | restriction `χ_{k,Λ}` and extension of regular `V_out` into `Λ` | [IV] (1.74)-(1.75) | unchanged | citation | 0 |
| V1 | constrained minimiser `V̂_Λ(W, V_out)` for the two-scale determining set: existence, uniqueness, regularity `O(B5 M^5)(ε_k + ε_{k+1})`, analyticity in `(W, V_out)` | [IV] Prop. 1, (1.77)-(1.80); [V] (1.12)-(1.13), (1.38)-(1.45); `[15]` Sects. D, E, G | fixed point on `P_0 ∩ ker Q_{k+1}` | **paper**: reduces to `[15]` Theorem 1 (`S6-START.md` 2: frozen hole + funnel + `Λ'` at scale `k+1` are nested as sets); analyticity by `[15]` Proposition 9 | 2 |
| V2 | background `U_0(W)` regular on all scales in `Λ`; gauge; `χ''_k = 1` | [IV] (1.80)-(1.98) | same with block-axial gauge | open (routine) | 3 |
| D-mod | **Lemma D, moderate cores**: spread of the core's image shrinks by `θ = L^{1-d} + K r0 + K' ε` per step | new; analogue of [V] (1.31), (1.47) | `NOTE.md` 2.2-2.3 | **paper** + **Lean** (`balaban_star_dilution`, `spread_iterate_quadratic`, `norm_wsum_sub_wsum_le`); exact weights checked by `star_weights.py`; constants `K, K'` open (routine, [12]) | 2 |
| D-vortex | deterministic Lemma D for all cores is **false** (centre vortex persists under every covariant symmetric average) | new; [I] (0.4), [IV] (1.2)-(1.9) | `NOTE.md` 2.4 | **Lean** (`vortex_persists`, `su2NegOne`) + paper (Balaban's average has the hypotheses) | done |
| D-shift | shift-averaged blocking leaves every blocked law unchanged | new | `NOTE.md` 2.5 | paper (exact, short); **not needed** after D-N | 0 |
| D-prob | **Lemma D-prob**: under i.i.d. uniform shifts a deep core stays deep for `n` steps with probability `≤ p_stayⁿ`, `p_stay = O(L^{1-d})` | new | `NOTE.md` 2.5; missing: cone bound `f(z) ≤ C |z - y'|^{1-d}` on the path fraction, multi-site bookkeeping | **ruled out as a device** (`D-N.md` 2: shifts buy `≤ L^{-d}` per step, Balaban charges `exp(O(1) log g^{-2}(MR)^d)` per step); the estimate itself not needed | 0 |
| D-N | constants: D-prob needs `N ≳ p0(g)/((d-1) log L)`, i.e. `ν ≥ p0`; compatible with `½ν ≤ p0 - p1 - 1` iff `p0 ≥ 2p1 + 2`; recent-region entropy then at equal powers (`A0 > 4 log L` times a constant) | [IV] p. 198; [V] p. 363, (1.80)-(1.85), p. 389 | `D-N.md` | **answered (paper)**: `N ≈ p0/(d log L)` admissible after removing the [IV] p. 198 artefact (`g_k/g_h ≤ √2`) and retuning `p0 > (2d+6) r`, `(p0+(2d+6)r)/2 < p1 < p0`, `β0` small; does not rescue the shift device | done |
| D-pin | **deep cores pinned at nested block centres**: root rule (one root per core, suppression charged once, core carried as a Z2 label plus a frozen hole) | new | `D-PIN.md`, `P0.md`, `TWIST.md`, `P2-PRIME.md` | **SURVIVES WITH LEMMAS**: P0 (written), NT′ (cut avoidance, open), P2′ (proof given Balaban bounds I1-I3), P4 (citation level); root bookkeeping paper | see P-rows |
| TRAP | **trapping of deep cores**: still deep after a fixed delay `N_t ∈ {0, 1, 2}` ⇒ frozen hole, excised from the block average (per-block canonical filling), record kept; root once + maintenance (P2′) | new (the owner's proposal, `../../PREP.md`) | `TRAP.md` | **paper** (accounting and design); open checks T1 filling regular, T2 link RP of the excised blocking, T3 P2′ with excision, T4 filling mismatch small | 3 |
| P0 | **twisted blocking**: Z2 label field + smooth part blocked by (0.4) + straight-path decimation of labels; creation at isolated centre patterns, drop on contradiction | new; [I] (0.4), p. 254 | `TWIST.md`, `P0.md`; `Twist.lean`; `lattice_twist.py`, `twist_dynamics.py` | definition, small-field identity, covariance, symmetry, locality, link RP: **Lean + paper**; no trapping: **numerical** (`d = 2, 3` multi-level; `d = 4` one-site `L = 13` and full lattice `L = 3`, 2 steps); proof open | optional since TRAP (labels for centre-valued cores) |
| P2′ | **subscale hole decoupling**: `|Δ_k| ≤ C[ρ_k^{d-2}(1 + p0²) + ρ_k^{(d-2)/2} p0 (1 + a^{1/2}/g_h)]`, `ρ_k = D0 L^{-(k-h)}`; summed `≪ a/g_h²` | new; [13], [II], `[15]` Thm 1 and (9)-(10); [I] (1.18), [II] (2.41), [III] (2.31), (2.42) | `P2-PRIME.md` v2 | **proof** given I1-I3: capacity lemma (proved), soft constraint, determinant, background (proved given I1, I2), hole as data in `[15]` (checked), local terms (I3, Balaban's analyticity as black box) | 3 (write-up) |
| NT′ | **cut avoidance**: (a) every star has a sign pattern with corrected relative angles `≤ θ_root < π`; (b′) at most `N_cut` near-cut steps over a pinned core's orbit. Replaces uniform no trapping, which fails (slow balanced stars) | new | `NO-TRAP.md`, `NT-A.md`, `NT-B.md` | (a) **proved**: `θ_root = 2 arccos s_8 = 168.7°` (union bound on `S³`, paper; cap half **Lean** `CutAvoid.lean`); (b′) **reduced** to the one-step **Cap Lemma** (the star map keeps every cap of radius `< 90°`; then `N_cut = 0`), open, numerically supported (300-step orbits, fixed-cap test up to 89°) | 0 (off the critical path since TRAP) |
| P3 | rate condition `A_min b log L > C_1`, `b = 22/(6π²) ≈ 0.37` (not needed if P2′ holds) | [III] (2.42), [I] Thm 2 | `D-PIN.md` 4(b) | open (constants) | 1 |
| P4 | root suppression of a deep core `exp(-A_min/g_h²)`, `A_min = c0 r0²` | `[15]` Thm 1; [V] p. 380 | `D-PIN.md` 4 | citation level | 1 |
| E1 | linear term: `J_0 = Q*_{k+1} λ` on `Λ`; its core contribution `≤ g_k^{-2} ε_{k+1} θ^{n_mod} r0 ≪ 1` | [V] (1.2)-(1.6), (1.28)-(1.29), p. 363 | Lagrange-multiplier identity, D-mod | **paper**: exact identity (critical point on `Q δA' = 0`, `S6-START.md` 3); no core term (frozen hole) | 0.5 |
| E2 | quadratic form positivity on `ker Q_{k+1}` | [V] (1.7)-(1.9) | Poincare bound `O(L²)` (better) | **paper**: restriction of a positive form (`S6-START.md` 3) | 0.5 |
| E3 | denominator `D_X(W) = exp[-g_k^{-2}A(ζ0, U_0(W)) - Î + Ê_k(Λ)]`, `|Î| ≤ O(1)M^5 + O(log g_k^{-2})` per constrained bond; Wilson term cancels | [V] (1.10)-(1.11), (1.30)-(1.37) | W-dependent, analytic, non-zero on regular `W` | **paper** (carry-over pinned to [V] (1.2)-(1.22), `E3.md`): exact Wilson cancellation around `Û_0(W)`; normalisation shift cancels in `N/D`; Poincaré (1.8) for the block-axial gauge to re-prove | 1 |
| E4 | localization of the `W`-dependence | [V] (1.14)-(1.69), pp. 359-376 (pp. 364-373 now read) | enters only through `U_0(W)` and shell shifts | citation + D-mod (moderate); P0, P2′ (deep) | 1 |
| E5 | `T̂'_k(X)` and matched normalisations `E_k(X)`, `(-½ d(g) log g^{-2} + log σ0)|B0 \ T0|` | [V] (1.70)-(1.71) | numerator and denominator constrain the same bonds | open (routine) | 2 |
| E6 | analytic extension `|T'(X,(U,J))F| ≤ T'(X)1 e^{sup|σ|} sup|F|` and lower bound | [V] (1.73)-(1.75) | needs (D1): D-mod for moderate cores; deep cores: D-pin | open (routine given D-mod; deep cores: P0, P2′) | 2 |
| E7 | large-field factors under δ-constraints (pointwise; group integrals with δ bounded by the Jacobian `O(1)^{|Λ|}`) | [V] (1.76)-(1.79) | uniform in regular `W` | open (routine) | 2 |
| E8 | entropy induction `κ_j(Z)` | [V] (1.80)-(1.88) | extra `O(1)` per step from the `W` partition and Jacobians | open (routine) | 2 |
| E9 | fundamental inequality `sup_{W reg} N_X(W)/D_X(W) ≤ exp(-2(1+β0)^{-1} p0(g_k))` | [V] (1.89) | changed constants | open (routine) | 1 |
| E10 | fresh factor in branch (a) (D2) | ONE-STEP 2.3 | moderate cores: D-mod + the regularity theorem (Theorem 1 of `[15]` as ONE-STEP cites it; to be checked against `[15]`); deep cores at nested centres: **false** (D-vortex), shifts do not help (D-N) | moderate: paper (NOTE 2.3); deep: root rule (D-pin) | 1 |
| E11 | polymer gas, vacancy-1, activities `|F| ≤ c1 exp(-(1+β)κ d(X'))` | [V] (1.90)-(1.97) | activities depend on `W` on `Λ_j`: local on the same domains | citation (check) | 0.5 |
| E12 | exponentiation, new R-terms `|R''(X)| ≤ exp(-p0) exp(-κ d_k(X))`, new action | [V] (1.98)-(1.101), p. 389 | unchanged | citation (check) | 0.5 |
| E13 | final form `R̂ρ_k` in the form [III] (2.18); next `T` | [V] (1.102)-(1.104); [III] Sect. 3 | unchanged; `T R̂ρ_k` is the law (X1) | citation | 0.5 |
| ext | running coupling stays below `γ` | [I] Theorem 2 (unpublished) | independent of M1 | open (external) | — |

## Totals

* **Done:** X1, P0 algebra and positivity, D-mod core, D-vortex, NT′(a) cap half (**Lean**: 34 theorems in `Exact.lean`,
  `Dilution.lean`, `Vortex.lean`, `Twist.lean`, `CutAvoid.lean`); D-N, root bookkeeping, link reflection positivity of the
  twisted blocking, P2′ given Balaban's bounds I1-I3, NT′(a), V1 from `[15]`, E1 (identity), E2, E3, X1.H2, the trapping
  accounting (**paper**); the `d = 4`, `L = 13` off-centre step, local contraction, long orbits, the fixed-cap test
  (**numerical**); reading of [IV] pp. 177-199, [V] pp. 355-386, `[15]` pp. 277-292, 303-309.
* **Open, new:** trapping checks T1-T4 (`TRAP.md` 0.6).
* **Off the critical path (kept):** the Cap Lemma, the Z2 labels (alternative for centre-valued cores).
* **False as first stated:** deterministic Lemma D (vortex), uniform no trapping (slow balanced stars).
* **Open, routine:** S1, X1.H1, X2, V2, D-mod constants, E5-E13 under the block constraint, P4, the P2′ write-up: about
  33 pages, plus re-reading about 40 pages of Balaban.
* **External:** [I] Theorem 2.

## Order of work (recommended)

1. §6 continued: E5-E9 (E3 done on paper, `E3.md`; its Poincaré step for the block-axial gauge to re-prove).
2. Trapping checks T1-T4 (`TRAP.md`).
3. A Lean assembly theorem for §8 with the open estimates as named hypotheses.
4. The routine rows, then the write-up of the paper.
