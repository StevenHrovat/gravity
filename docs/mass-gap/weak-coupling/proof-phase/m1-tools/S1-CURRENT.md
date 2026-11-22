# S1 for the current main line: the inductive form and one step (m1-tools, 2026-11-22)

Brief (REVIEW-2 G1): rewrite the one-step induction for laws for the current design: state `Form_k` for the law of
`(V_k, τ'_k)` (with the labels and the randomised bonds), and the one-step bookkeeping, re-checking the E-rows for what
changes. Supersedes `S1-PROOF.md` and the record parts of `S1-ROWS.md`. Claim marks as in `NOTE.md`.

## 0. Result in plain words

`Form_k` is Balaban's [III] (2.18) for the SO(3) block field, with three additions:
* the closed Z2 layer `τ'_k`, entering only through explicit label factors;
* excision holes and randomised swallowed bonds, which live only inside large-field regions;
* the decoder's conflict components, which enlarge large-field regions at the bare scale.

One step is Balaban's step with the conditional step on small-field domains, excision before blocking, and release
with labelled Mayer polymers kept explicit. Every E-row is checked below against what changes. Two points stay at
sketch level: the mixed Mayer expansion with explicit label factors (G2) and R10's insertion bookkeeping. **Status:**
paper outline with explicit deltas; no row is open beyond those two.

## 1. State, law, `Form_k`

* **State at scale `k`:** an SO(3) field `V_k` on the scale-`k` bonds and a closed Z2 cochain `τ'_k` on the scale-`k`
  plaquettes. The block map: at the bare scale `τ'_0 = σ*(sign tr U_p)` (decoder) and `V_0 = Ad U`. At each step:
  excision and filling of the deep SO(3) structures (twist-free envelopes, `FILL.md`, `REVIEW2-RESPONSE.md` 3);
  Balaban's average (0.4) of the filled field; independent Haar values on the swallowed coarse bonds
  (`SKETCH-STEPS.md` 1); `τ'_{k+1} = Stokes(τ'_k)`.
* **Law:** `ρ_k` is the density of `(V_k, τ'_k)` under `ym ⊗ Haar^{noise}` (Lean: `Exact.lean`;
  `Interface/RandBlocking.lean`).
* **`Form_k(ρ)`:**
  `ρ(V, τ') = Σ_{(Ω_j, Λ_j, Z_j)} Σ_{ℓ ~ τ'} (Π_ℓ a_ℓ) · T_k(Z_k)[ χ_k(Λ_k) exp( A_k(V, U_k(V), 𝒜) + Σ_ℓ log(1 + h_ℓ) ) ]`.
  * **(F-a) domains:** Balaban's admissible sequences; large-field regions enlarged by the decoder's conflict
    components and by the excision envelopes.
  * **(F-b) background:** Balaban's minimiser `U_k(V)` ([15], carried over to SO(3), R9). Holes never lie in
    small-field domains, so **no excision inside V1**: `V1-EXCISION.md` and `V1-INPUTS.md` are not needed on this line.
  * **(F-c) small field:** SO(3)-regular ((2.17) with the SO(3) distance); no condition on `τ'` (G2).
  * **(F-d) `T_k`:** Balaban's (2.19)-(2.22). On small-field domains, the conditional step's fibre integrals. Inside
    large-field regions, excised hole contents are integrated freely (no constraint reads them) and swallowed bonds are
    integrated against Haar.
  * **(F-e) action:** E-, R-, B-terms as in [III] (2.23)-(2.42). Released large fields (deep SO(3) structures, acts,
    monopole loops, halos) are R-terms with (2.31) bounds. Their field dependence is of dimension 4 (R8).
  * **(F-f) labels:** `ℓ ~ τ'` runs over label decorations producing `τ'`. Each has a constant `|a_ℓ| ≤ e^{-16/g_0²}
    poly(β)` per labelled skeleton bond and a small analytic, local, gauge-invariant `h_ℓ` (`REVIEW2-RESPONSE.md` 2).
  * **(F-g) symmetries:** gauge invariance of every term. Euclidean covariance (2.29), (2.32) holds except for the
    fixed tie-breaks (decoder, swallowed rule), which act only on rare events inside large-field regions. The
    covariance is then that of the sums over positions, up to terms bounded by those events' activities.

## 2. One step, `k → k + 1`

| # | operation | rows | what changed from Balaban / the old notes |
|---|---|---|---|
| 0 | (bare only) split `U ↦ (Ad U, sign tr U_p)`, decoder | `ROUTE-B.md` 1, `CLOSING.md`, `REVIEW2-RESPONSE.md` 1 | new; decoder locality by the conflict-graph Peierls bound |
| 1 | preparatory operations ([IV] (1.10)-(1.99)), domains | P1, P2 | none (SO(3), R9) |
| 2 | excision of deep SO(3) structures; filling; swallowed bonds randomised | `FILL.md`, `REVIEW2-RESPONSE.md` 3, `SKETCH-STEPS.md` 1 | new; inside large-field regions only |
| 3 | gauge fixing (block-axial) | X2 (Lean leaf + paper) | none |
| 4 | conditional step on small-field domains | X1, X1.H1, X1.H2 (Lean) | none |
| 5 | background and its regularity | V1 ([15], SO(3)), V2 | simpler: no holes in small-field domains |
| 6 | linear term, quadratic form, denominator, localisation | E1, E2, E3 (`POINCARE.md`), E4 | none beyond SO(3) constants |
| 7 | large-field regions: normalisations, analytic extension, factors, fibre mass, entropy, fundamental inequality | E5, E6, E7, E7.J, E8, E9 | E7.J only at regular `W`, with envelopes and randomised swallowed bonds (`FILL.md`); E8 as written ([V] (1.80)-(1.81), `R10-SCOPE.md` 1); E6: fillings analytic in the data where used |
| 8 | dilution and regularity of what is carried | R1 (`OFFCENTRE.md`), R2 (`R2-REPAIR.md`) | new rows replace D-mod |
| 9 | release: Mayer expansion, labelled polymers explicit, exponentiation of the rest | E11, E12, `REVIEW2-RESPONSE.md` 2 | labelled parts kept as factors `a_ℓ(1 + h_ℓ)` (sketch) |
| 10 | final form at `k + 1`; next `T` | E13 | form of section 1 |

## 3. `Form_{k+1}`, item by item

* **(F-a)** Balaban's new sequences, plus the envelopes created at this step, plus the decoder components (bare step).
* **(F-b), (F-c)** V1, V2 on SO(3)-regular domains.
* **(F-d)** Balaban's `T` plus the conditional step (Lean exactness), hole contents and noise integrated.
* **(F-e)** E- and R-terms from E11, E12. Released terms have dimension-4 coupling (R8).
* **(F-f)** labels from step 9.
* **(F-g)** as stated.

## 4. What this supersedes, and what remains

* **Superseded:**
  * `S1-PROOF.md` (status line: broken);
  * `S1-ROWS.md` (records);
  * the "trapping at creation" set-up of `E7J.md` 1 (replaced by `FILL.md`'s rule; the slicing argument of `E7J.md` 2
    is unchanged);
  * `E5-E9.md`'s references to trapped records (E5-E9 hold as Balaban's, with the deltas of section 2).
* **Sketch level:**
  * G2's mixed expansion;
  * R10's insertion bookkeeping (UV half, `REVIEW2-RESPONSE.md` 5).
* **Citation:** Balaban [I]-[V], [12]-[16] for SO(3) (R9, with the amended row 1).
* **Lean:** `Assembly.lean`'s rows now name the current design (`Decoder`, `Labels`, `Release`, `Excision`); assembly
  remains bookkeeping.
