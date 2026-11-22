# M1 plan: every estimate a law-preserving large-field step needs (m1-tools, 2026-11-22)

M1 = Balaban's R operation ([IV], [V]) redone so that the effective densities stay the **laws** of the block fields:
the step `R̂` resamples the current field on `Λ` inside the fibre of the next block field `W` (ratio `N(W)/D(W)`,
`../c6f-m1scope/ONE-STEP.md` 2.1). This file lists every estimate M1 needs, from ONE-STEP's table 2.3 plus the rows
this session added (`NOTE.md`), with source equations, status and size. No write-up of M1 itself.

**Status keys.** **Lean**: machine-checked here (`formal/ProofPhase/M1/`). **paper**: proved on paper in `NOTE.md`.
**citation**: carries over from Balaban with the given equations, re-read line by line under the block constraint.
**open**: to be written (routine = same proof, changed constants; new = needs an idea or a lemma not in Balaban).
**Size**: journal pages in Balaban's density, new writing (re-reading not counted).

## Table

| # | estimate | Balaban source | M1 version | status | size |
|---|---|---|---|---|---|
| S1 | inductive form for laws: (2.18) with R-terms allowed to depend on `U_k` through `M(U_k)` on `Λ`; block-axial gauge on `Λ`; the `W` partition `1 = χ(W reg) + χ^c(W reg)` and branch (a) | [III] (2.17)-(2.42); [IV] (0.2)-(0.6) | restate for laws; branch (a) terms are current large fields of `V_{k+1}` | open (routine) | 5 |
| X1 | **exactness** `T R̂ = T`, term by term | [IV] (1.99), (1.102) (where Balaban loses it) | `map_resample_eq`, `map_comp_resample_eq`, `sum_map_resample_eq`, `map_resample_rnDeriv_eq` | **Lean** (given H1, H2 below) | done |
| X1.H1 | `N`, `D` are the δ-integrals against fibre Haar measure (fibre representation) | [I] (0.13); [12] | block map a submersion on regular configurations | open (routine) | 1 |
| X1.H2 | `0 < D(W) < ∞` for regular `W` | [V] (1.10)-(1.11) | the constrained minimiser lies in the fibre and in the support of `ŵ` | open, follows from V1 | in V1 |
| X2 | gauge-fixing removal (L3) exact inside `T` | [V] p. 378; [I] (0.14)-(0.16) | Faddeev-Popov with block-axial gauge, Jacobian 1 | open (routine) | 1 |
| P1 | preliminary integrations | [IV] (1.10)-(1.99), pp. 177-193 | unchanged; all operations exact (read in full, `NOTE.md` 1.1) | **citation** (confirmed) | 0 |
| P2 | restriction `χ_{k,Λ}` and extension of regular `V_out` into `Λ` | [IV] (1.74)-(1.75) | unchanged | citation | 0 |
| V1 | constrained minimiser `V̂_Λ(W, V_out)` for the two-scale determining set: existence, uniqueness, regularity `O(B5 M^5)(ε_k + ε_{k+1})`, analyticity in `(W, V_out)` | [IV] Prop. 1, (1.77)-(1.80); [V] (1.12)-(1.13), (1.38)-(1.45); `[15]` Sects. D, E, G | fixed point on `P_0 ∩ ker Q_{k+1}` | citation: `[15]` Theorem 1 (pp. 278-279) covers nested sets coarser inside; check its distance condition (1) for `Λ ⊂ Z` (`D-N.md` 5); analyticity from `[15]` later sections | 5 |
| V2 | background `U_0(W)` regular on all scales in `Λ`; gauge; `χ''_k = 1` | [IV] (1.80)-(1.98) | same with block-axial gauge | open (routine) | 3 |
| D-mod | **Lemma D, moderate cores**: spread of the core's image shrinks by `θ = L^{1-d} + K r0 + K' ε` per step | new; analogue of [V] (1.31), (1.47) | `NOTE.md` 2.2-2.3 | **paper** + **Lean** (`balaban_star_dilution`, `spread_iterate_quadratic`, `norm_wsum_sub_wsum_le`); exact weights checked by `star_weights.py`; constants `K, K'` open (routine, [12]) | 2 |
| D-vortex | deterministic Lemma D for all cores is **false** (centre vortex persists under every covariant symmetric average) | new; [I] (0.4), [IV] (1.2)-(1.9) | `NOTE.md` 2.4 | **Lean** (`vortex_persists`, `su2NegOne`) + paper (Balaban's average has the hypotheses) | done |
| D-shift | shift-averaged blocking leaves every blocked law unchanged | new | `NOTE.md` 2.5 | paper (exact, short); **not needed** after D-N | 0 |
| D-prob | **Lemma D-prob**: under i.i.d. uniform shifts a deep core stays deep for `n` steps with probability `≤ p_stayⁿ`, `p_stay = O(L^{1-d})` | new | `NOTE.md` 2.5; missing: cone bound `f(z) ≤ C |z - y'|^{1-d}` on the path fraction, multi-site bookkeeping | **ruled out as a device** (`D-N.md` 2: shifts buy `≤ L^{-d}` per step, Balaban charges `exp(O(1) log g^{-2}(MR)^d)` per step); the estimate itself not needed | 0 |
| D-N | constants: D-prob needs `N ≳ p0(g)/((d-1) log L)`, i.e. `ν ≥ p0`; compatible with `½ν ≤ p0 - p1 - 1` iff `p0 ≥ 2p1 + 2`; recent-region entropy then at equal powers (`A0 > 4 log L` times a constant) | [IV] p. 198; [V] p. 363, (1.80)-(1.85), p. 389 | `D-N.md` | **answered (paper)**: `N ≈ p0/(d log L)` admissible after removing the [IV] p. 198 artefact (`g_k/g_h ≤ √2`) and retuning `p0 > (2d+6) r`, `(p0+(2d+6)r)/2 < p1 < p0`, `β0` small; does not rescue the shift device | done |
| D-pin | **deep cores pinned at nested block centres**: the owner's root rule (one root per core, suppression charged once, core frozen and carried) | new | `D-PIN.md` | **scoped: SURVIVES WITH LEMMAS P0, P2 (P3 fallback), P4**; root bookkeeping proved on paper (`D-PIN.md` 3) | see P-rows |
| P0 | **averaging design**: an admissible average equal to Balaban's (0.4) on the small-field regime, analytic near every centre-valued star pattern, no trapping elsewhere (Balaban's own average is discontinuous at pinned patterns; first smooth variant traps 33% of deep stars) | new; [I] (0.4), p. 254 | `D-PIN.md` 2.2-2.4; `star_dynamics.py`, `near_vortex.py`, `zlift_traps.py` | **open, decisive** (would BREAK here if no such average exists) | ? |
| P2 | **subscale decoupling**: a frozen root `m` steps old changes the step's ratio `N/D` by `exp(O(C L^{-c m}))` | new; evidence [V] (1.31), (1.47) | `D-PIN.md` 2.1 | open (new) | 3 |
| P3 | rate condition `A_min b log L > C_1`, `b = 22/(6π²) ≈ 0.37` (only if P2 fails) | [III] (2.42), [I] Thm 2 | `D-PIN.md` 4(b) | open (constants) | 1 |
| P4 | root suppression of a deep core `exp(-A_min/g_h²)`, `A_min = c0 r0²` | `[15]` Thm 1; [V] p. 380 | `D-PIN.md` 4 | citation level | 1 |
| E1 | linear term: `J_0 = Q*_{k+1} λ` on `Λ`; its core contribution `≤ g_k^{-2} ε_{k+1} θ^{n_mod} r0 ≪ 1` | [V] (1.2)-(1.6), (1.28)-(1.29), p. 363 | Lagrange-multiplier identity, D-mod | open (routine + D-mod) | 2 |
| E2 | quadratic form positivity on `ker Q_{k+1}` | [V] (1.7)-(1.9) | Poincare bound `O(L²)` (better) | open (routine) | 1 |
| E3 | denominator `D_X(W) = exp[-g_k^{-2}A(ζ0, U_0(W)) - Î + Ê_k(Λ)]`, `|Î| ≤ O(1)M^5 + O(log g_k^{-2})` per constrained bond; Wilson term cancels | [V] (1.10)-(1.11), (1.30)-(1.37) | W-dependent, analytic, non-zero on regular `W` | open (routine) | 2 |
| E4 | localization of the `W`-dependence | [V] (1.14)-(1.69), pp. 359-376 (pp. 364-373 now read) | enters only through `U_0(W)` and shell shifts | citation + D-mod (moderate); D-pin, P2 (deep) | 1 |
| E5 | `T̂'_k(X)` and matched normalisations `E_k(X)`, `(-½ d(g) log g^{-2} + log σ0)|B0 \ T0|` | [V] (1.70)-(1.71) | numerator and denominator constrain the same bonds | open (routine) | 2 |
| E6 | analytic extension `|T'(X,(U,J))F| ≤ T'(X)1 e^{sup|σ|} sup|F|` and lower bound | [V] (1.73)-(1.75) | needs (D1): D-mod for moderate cores; deep cores: D-pin | open (routine given D-mod; deep cores: P0) | 2 |
| E7 | large-field factors under δ-constraints (pointwise; group integrals with δ bounded by the Jacobian `O(1)^{|Λ|}`) | [V] (1.76)-(1.79) | uniform in regular `W` | open (routine) | 2 |
| E8 | entropy induction `κ_j(Z)` | [V] (1.80)-(1.88) | extra `O(1)` per step from the `W` partition and Jacobians | open (routine) | 2 |
| E9 | fundamental inequality `sup_{W reg} N_X(W)/D_X(W) ≤ exp(-2(1+β0)^{-1} p0(g_k))` | [V] (1.89) | changed constants | open (routine) | 1 |
| E10 | fresh factor in branch (a) (D2) | ONE-STEP 2.3 | moderate cores: D-mod + the regularity theorem (Theorem 1 of `[15]` as ONE-STEP cites it; to be checked against `[15]`); deep cores at nested centres: **false** (D-vortex), shifts do not help (D-N) | moderate: paper (NOTE 2.3); deep: **open**, see D-pin | 1 |
| E11 | polymer gas, vacancy-1, activities `|F| ≤ c1 exp(-(1+β)κ d(X'))` | [V] (1.90)-(1.97) | activities depend on `W` on `Λ_j`: local on the same domains | citation (check) | 0.5 |
| E12 | exponentiation, new R-terms `|R''(X)| ≤ exp(-p0) exp(-κ d_k(X))`, new action | [V] (1.98)-(1.101), p. 389 | unchanged | citation (check) | 0.5 |
| E13 | final form `R̂ρ_k` in the form [III] (2.18); next `T` | [V] (1.102)-(1.104); [III] Sect. 3 | unchanged; `T R̂ρ_k` is the law (X1) | citation | 0.5 |
| ext | running coupling stays below `γ` | [I] Theorem 2 (unpublished) | independent of M1 | open (external) | — |

## Totals

* **Done here:** X1 (Lean), D-mod elementary part (Lean) with the exact weights (paper + exact-fraction check),
  D-vortex (Lean + paper), D-N (paper, `D-N.md`), D-pin scoping with the root bookkeeping (paper, `D-PIN.md`),
  reading of [IV] pp. 177-199 and [V] pp. 364-386 (P1, E4 confirmed), `[15]` Theorem 1 statement.
* **New writing, routine:** S1, X1.H1, X2, V1 check, V2, D-mod constants, E1-E3, E5-E9, moderate E10, retuning of
  `p0, p1, β0` (`D-N.md` 1), P4: about 34 pages, plus re-reading about 40 pages of Balaban.
* **Open, new:** P0 (averaging design, decisive), P2 (subscale decoupling, about 3 pages if it holds), P3 only as a
  fallback.
* **M1's verdict now:** survives for moderate cores; for deep pinned cores **survives with lemmas P0 and P2** under the
  owner's root rule; P0 is where it would break.

## Order of work (recommended)

1. P0 exploration (numerical first, `star_dynamics.py` as the harness): averages equal to (0.4) on the small-field
   regime, analytic at centre-valued patterns, tested for trapping with trivial and with random small-field shells.
2. P2 on paper (subscale hole capacity in `d = 4`, adjoint triviality of centre-valued patterns, against [V] (1.31),
   (1.47)).
3. V1 with `[15]` Theorem 1 (check its condition (1) for `Λ ⊂ Z`), then E1-E3, E9.
4. The routine rows, with the retuned exponents of `D-N.md` 1.
