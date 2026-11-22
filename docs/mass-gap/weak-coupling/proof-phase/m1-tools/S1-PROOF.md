# §8: the S1 bookkeeping, one step of the inductive form for laws (m1-tools, 2026-11-22)

> **Status (2026-11-22): broken by REVIEW-1 F1** (`../m1-review/REVIEW-1.md`): the root count here assumes one position per cell per scale, valid only for cores pinned at nested centres, while trapping traps every deep plaquette; records are then dense in physical units and the bounds are not uniform. Assessment and repair attempt: `F1-REPAIR.md`. The text below is left as it was.

Brief: write the bookkeeping that proves S1 (`assemble` in `Assembly.lean`): if `ρ_k` has the inductive form `Form_k`
(`S1-ROWS.md` 1) and every row holds at scale `k < K`, then `ρ_{k+1}` has `Form_{k+1}`. Not the paper write-up. Read for
this note: [V] pp. 387-391 ((1.90)-(1.104)) and [III] Sect. 2 again; everything else is in the notes cited per step.
Lean: `formal/ProofPhase/M1/Assembly.lean` (`m1_assembly_rows_upTo`), `Routine.lean` (`record_gas_le`). Claim marks as
in `NOTE.md`.

## 0. Result in plain words

1. **S1 is proved on paper.** One renormalisation step is a fixed sequence of operations (section 2); each changes
   the components of `Form` in a way some row controls, and at the end every item (F-a)-(F-g) of `Form_{k+1}` is
   checked (section 3). With `m1_assembly_rows_upTo` (**Lean**) this gives the main theorem: the form at every scale
   `k ≤ K`, and the laws at every scale.
2. **Two corrections to `S1-ROWS.md` 1, found while writing it out** (neither changes a row's status):
   * the maintenance of a decoupled record (P2′) is a **factor of the record's weight** `w_r`, not a B-term: its size
     `C(1 + p0²)` exceeds the B-term bound (2.42), but it is far below the record's own suppression;
   * the root action is **defined** as `a_r = A_min n_r` (`n_r` the record's number of deep plaquettes), the bound P4
     actually proves pointwise, not as the action of the frozen content. P2′'s cross term then reads
     `(C n_r)^{1/2}/g_s` in place of `a^{1/2}/g_s`, with the same conclusion.
3. **The record gas is dilute.** Summing the record weights over all record sets in a volume `|T|` gives at most
   `exp(|T| · sup w)` (**Lean** `record_gas_le`), with `sup w ≤ exp(-A_min/(2 g²))`: records change the free energy
   per site by at most `exp(-A_min/(2g²))`, far below Balaban's `exp(-p0)`.
4. **Order of constants** (section 5): `d`, then `L`, then `r0 = c/L²`, `R_sep(d, L)`, then Balaban's
   `M, R_j, p0, p1, κ, β0` (depending on `d, L`), then `γ0(L)`; the coupling input must supply `γ ≤ γ0(L)`. No
   circularity.

## 1. What is proved

**Theorem (M1, main).** Let `K` be the stopping scale (`g_k ≤ γ` for `k < K`, [I] Theorem 2). Under the data
hypotheses of `M1Hypotheses` (measurability, factorisation of the blocking, fibre representation X1.H1, `0 < D < ∞`
X1.H2, the definition of `T`, the bare law) the renormalisation-group density `ρ_k` is the law of `(V_k, 𝓡_k)` for every
`k`, and has `Form_k` for every `k ≤ K`. *Proof:* `m1_assembly_rows_upTo` (**Lean**) from `form0` (Balaban's bare form
plus "no records" at `k = 0`, with records created at `k = 0` from bare plaquettes at angle `≥ r0`, treated as in
step 5 below) and from S1 below the horizon, proved in sections 2-3.

## 2. One step, `k → k + 1`, in order

Each line: the operation, what it does to `Form`, the row that controls it.

| # | operation | effect on the form | rows |
|---|---|---|---|
| 1 | Balaban's preliminary operations ([IV] (1.10)-(1.99)): decompositions of unity for the next field, the new characteristic functions, the preliminary integrations | identities; produce the large-field regions of `V_{k+1}` and the R-operation input [IV] (1.99), (1.100) | P1, P2 |
| 2 | **Records created** at `k + 1`: every plaquette of `V_{k+1}` at angle `≥ r0` starts a record (hole = component, merged at distance `< R_sep`); the hole's bonds leave the next block average (excision, per-block filling) | the record set `𝓡_{k+1}` = images of the old records + new ones; new holes lie in large-field regions of `V_{k+1}` (`r0 ≫ ε_{k+1}`), so in `Z_{k+1}` | TRAP (a), (b) |
| 3 | Gauge fixing in block-axial gauge (forest rooted at the block centres and at record sites) | exact, Jacobian 1 | X2 |
| 4 | On each small-field component `Λ` of the step: the **conditional step** `R̂` (resample `V_k|Λ` in the fibre of `(W, V_out, 𝓡)`, ratio `N/D`; branch (a) for regular `W`, branch (b) left as it is) | the law of `(V_{k+1}, 𝓡_{k+1})` is unchanged (`map_comp_resample_eq`); the term's `W`-dependence now enters through `N/D` | X1, X1.H1, X1.H2 |
| 5 | Background for regular `W`: the constrained minimiser with records excised, its regularity on all scales | background `U_0(W)` of `Form_{k+1}` (F-b) | V1, V2 |
| 6 | Expansion of `D(W)`: linear term, quadratic form, determinant, cancellation of the Wilson term; localisation of the `W`-dependence | `D(W) = exp[-g_k^{-2} A(ζ0, U_0(W)) - Î + Ê_k(Λ)]`; `N/D` written as local terms | E1, E2, E3, E4 |
| 7 | Large-field regions of the step: normalised operations, analytic extension, large-field factors with the fibre mass, entropy, fundamental inequality | each large-field domain `X` gives `sup_W N_X/D_X ≤ exp(-2(1+β0)^{-1} p0(g_k))` | E5, E6, E7, E7.J, E8, E9 |
| 8 | Cores: moderate cores dilute (the fresh factor of branch (a)); old records: carrying (in `Z`) or decoupled (in `Λ`, factor `exp(Δ_k)`); new records: root suppression | moderate cores leave the large-field region after `n_mod` steps; each record's weight `w_r` is multiplied by its step cost (section 4) | D-mod, TRAP (c), P2′, P4 |
| 9 | Mayer expansion, polymer activities, exponentiation, sorting into E-, R-, B-terms; new large-field region `Z_{k+1} = Z_k ∪ ⋃ Y_i ∪` new holes | the form (2.18) at `k + 1` | E11, E12, E13 |

## 3. `Form_{k+1}`, item by item

* **(F-a) domains.** Balaban's new sequences ([V] (1.101)-(1.102)) are admissible by his construction; the records
  added in step 2 lie in `Z_{k+1}`; an old record whose `ρ_{k+1} ≤ 1` and whose neighbourhood is `ε_{k+1}`-regular may
  leave `Z` (decoupled), the others stay in `Z` (carrying). Holes are `R_sep`-separated by the merging rule. ✓
* **(F-b) background.** For each small-field domain the background is V1's minimiser with the decoupled holes excised,
  on Balaban's new determining set ([V] (1.33)-(1.37)); V2 gives its regularity. ✓
* **(F-c) small-field condition.** The new `χ_{k+1}` comes from step 1 ([IV] decompositions), unchanged. ✓
* **(F-d) integrations.** `T_{k+1} = T_k ∘` (one-step operation of the form (2.21), with the conditional step's fibre
  integrals on small-field domains, and the R-operation's changes on large-field ones); factorisation over components
  of `Z_{k+1}` (2.19) holds because the conditional step and the excision are local (each reads only its own blocks).
  Record contents are conditioning variables: no operation integrates them after creation. ✓
* **(F-e) action.** E-terms: the small-field renormalisation as in [I] on the new domains, bounds [I] (1.18) (the
  conditional step does not change small-field E-terms: on regular `W` the ratio `N/D` contributes only through
  R-terms). R-terms: [V] (1.100), `|R'(X)| ≤ exp(-p0) exp(-κ d_k(X))`, now possibly depending on the next field through
  `M_B(U)` on `Λ`; Euclidean covariant for the symmetries keeping the block partition. B-terms: [V] (1.99), new boundary
  terms on domains meeting the large-field region, bound (2.42). Records contribute no E-, R- or B-term (correction
  above). ✓
* **(F-f) records.** Section 4. ✓
* **(F-g) symmetries.** Gauge invariance: every operation is gauge covariant (the conditional step because `φ` is,
  the excision because the filling is). Euclidean covariance of the position sums for the partition-preserving
  symmetries; records covariant as a set. ✓

## 4. Records: weights and the record gas

**Weight of one record.** At creation (scale `s`), P4 bounds the density pointwise on the configurations with the
record's deep plaquettes: the fine field in the fibre has at least `n_r/C_d` distinct fine plaquettes at angle
`≥ r1 = r0/(C_d L²)` (each fine plaquette lies in the blocks of at most `C_d` coarse plaquettes), each forced by a
characteristic function, so the integrand carries `exp(-c_P r1² n_r/(C_d g_s²))`; the fibre mass is bounded (E7.J).
Define `A_min = c_P r1²/C_d` and `a_r = A_min n_r`. The record's factor at scale `k` is
`w_r^{(k)} = exp(-a_r/g_s²) · Π_{j ≤ k} exp(c_j)` with `c_j` its costs at step `j`: root entropy (`≤ C n_r log g_s^{-2}`,
once), carrying (`≤ C polylog N_j(H)` per step), maintenance (`|Δ_j|`, P2′, decoupled steps). By the Corollary of
`P2-PRIME.md` 5, `Σ_j c_j ≤ C polylog (n_r + log D0 + n_mod) + C(1 + p0² + p0 (C n_r)^{1/2}/g_s) ≤ a_r/(2 g_s²)` for
`g_s ≤ γ0(L)`, uniformly in `k`. Hence `w_r^{(k)} ≤ exp(-a_r/(2 g_s²))` at every scale. The factor is an analytic
function of the fields within distance `O(1)` of the hole (Lemma E of P2′), as (F-f) requires. ✓

**The record gas.** For a finite set `P` of possible record positions with weights `w_r ≥ 0`,
`Σ_{𝓡 ⊆ P} Π_{r ∈ 𝓡} w_r = Π_{r ∈ P} (1 + w_r) ≤ exp(Σ_{r ∈ P} w_r)` (**Lean** `record_gas_le`). Records of `n` deep
plaquettes anchored at a site have at most `C_d^n` shapes (connected sets), and their contents are integrated against
Haar probability measure, so `Σ_{records at a site} w_r ≤
Σ_n C_d^n exp(-A_min n/(2g²)) ≤ 2 C_d exp(-A_min/(2g²))`: the records' total weight per site is
`exp(O(exp(-A_min/(2g²))))`, a free-energy change far below Balaban's `exp(-p0)` per unit. (Merged records only regroup
terms of this sum.)

## 5. Constants, in the order they are chosen

| order | constant | depends on | condition (source) |
|---|---|---|---|
| 1 | `d = 4` | — | — |
| 2 | `L` (odd) | `d` | `L ≥ L0(d)`: `θ ≤ ½` (D-mod), `L^{1-d}` small (`NOTE.md` 2.2) |
| 3 | `r0 = c/L²` | `L` | E7.J (`c ≤ c_d`), D-mod (`8 r0 ≤ 1/8`) |
| 4 | `R_sep` | `d, L` | FR-multi (`V1-INPUTS.md` 2) |
| 5 | `M, R_j, p0, p1, κ, β0, A_0, …` | `d, L` | Balaban's conditions ([III] Sect. 2, [V] (1.80)-(1.97)); `p0 ≥ 2p1 + 2` |
| 6 | `n_mod` | `L, g` | `θ^{n_mod} r0 ≤ g²` (D-mod) |
| 7 | `γ0(L)` | all above | `A_min γ^{-2} ≥ 4 p0(γ)`, `A_min^{1/2} ≥ γ p0(γ)`, `ε L² ≤ c_d` with `ε = γ p0(γ)`, Balaban's smallness conditions on `g` |
| 8 | `γ`, `K` | coupling input | `g_k ≤ γ ≤ γ0(L)` for `k < K` ([I] Theorem 2) |

Each constant depends only on earlier ones: no circularity.

## 6. Status

S1: **paper** (this note), its logical form **Lean** (`m1_assembly_rows_upTo`), the record gas **Lean**
(`record_gas_le`). Corrections to `S1-ROWS.md` (F-e), (F-f) applied there. M1 has no open row left; what it rests on
outside itself is listed in `EXTERNAL.md`.
