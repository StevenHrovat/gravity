/-
Proof phase, M1 tools (m1-tools): the assembly of M1 (§8 of the paper outline) with the open estimates as named
hypotheses (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/M1-PLAN.md`, Part A, §8.
-/

import ProofPhase.M1.Exact

/-!
# M1, assembled: the renormalisation-group densities are the true laws

**The statement.** Scales `k = 0, 1, 2, …` with configuration spaces `X k` (the block field at scale `k`, together with
the carried records of trapped cores) and reference measures `ν k`. The blocking `B k : X k → X (k+1)` (Balaban's
average, twisted/excised as in `TWIST.md`, `TRAP.md`) defines the **true laws** `trueLaw k`: the bare Wilson law pushed
forward `k` times.

The renormalisation group produces densities `ρ k`. One step: resample (`resample`, the conditional large-field step
`R̂`, with the conditioning variable `φ k` through which the next blocking factors) and push forward (`T`: the density
`ρ (k+1)` of the pushforward). M1's main theorem has two halves:

* **laws:** `ν k`-density `ρ k` **is** the true law at every scale — machine-checked here from the exactness theorem
  `map_comp_resample_eq`, under the named data hypotheses below;
* **form:** every `ρ k` has Balaban's inductive form with his bounds (`Form k`) — by induction from the named
  hypotheses `form0` (the bare density) and `stepEstimates` (the estimates of §5-§7 of the outline: dilution,
  trapping, P2′, the constrained step E1-E13), which are **not** proved in Lean.

**Named hypotheses and where they are argued** (`M1-PLAN.md`, Part B):

| field | content | row |
|---|---|---|
| `meas_*` | measurability of the maps and densities | (routine) |
| `factor` | the next blocking factors through the conditioning variable | X1, `P0.md` 4, `TRAP.md` |
| `fibreN`, `fibreD` | `N`, `D` are the fibre integrals of the term and of the reference kernel | X1.H1 |
| `D_ne_zero`, `D_ne_top` | `0 < D < ∞` on the regular set | X1.H2 (`S6-START.md` 3) |
| `nextDensity` | `ρ (k+1)` is the density of the pushforward of the resampled term (the definition of `T`) | — |
| `base` | the bare density is the bare law | — |
| `form0` | the bare density has the inductive form | [III] (2.18) at `k = 0` |
| `stepEstimates` | the inductive form propagates one step | §5-§7: D-mod, TRAP, P2′, P4, V1, E1-E13 |

**Row by row:** `M1RowStatements`, `M1RowHypotheses`, `m1_assembly_rows` split `stepEstimates` into the rows of
`M1-PLAN.md`, Part B, with S1 as the combining hypothesis.

**Claim level.** `m1_assembly` and `m1_assembly_rows` are proved (standard axioms). It makes the logical structure of M1 machine-checked: the
only things left to prove are the named hypotheses, and exactness (the law half) needs none of the estimates.
-/

open MeasureTheory Measure
open scoped ENNReal

noncomputable section

namespace ProofPhase.M1

universe u

variable {X Y : ℕ → Type u} [∀ k, MeasurableSpace (X k)] [∀ k, MeasurableSpace (Y k)]

/-- The true blocked laws: the bare law pushed forward by the blockings. -/
def trueLaw (B : ∀ k, X k → X (k + 1)) (μ0 : Measure (X 0)) : ∀ k, Measure (X k)
  | 0 => μ0
  | k + 1 => (trueLaw B μ0 k).map (B k)

/-- **The data of the renormalisation group with the conditional large-field step.** -/
structure M1Data (X Y : ℕ → Type u) [∀ k, MeasurableSpace (X k)] [∀ k, MeasurableSpace (Y k)] where
  /-- reference measures (product Haar, with counting measure on records) -/
  ν : ∀ k, Measure (X k)
  /-- the blocking -/
  B : ∀ k, X k → X (k + 1)
  /-- the conditioning variable of the step at scale `k` (next field on `Λ`, outside field, records) -/
  φ : ∀ k, X k → Y k
  /-- the rest of the blocking: `B k = ψ k ∘ φ k` -/
  ψ : ∀ k, Y k → X (k + 1)
  /-- reference measure on the conditioning variable -/
  lam : ∀ k, Measure (Y k)
  /-- the renormalisation-group densities -/
  ρ : ∀ k, X k → ℝ≥0∞
  /-- the reference (small-field) kernel -/
  w : ∀ k, X k → ℝ≥0∞
  /-- fibre integral of the term -/
  N : ∀ k, Y k → ℝ≥0∞
  /-- fibre integral of the reference kernel -/
  D : ∀ k, Y k → ℝ≥0∞
  /-- the regular set (branch (b)) -/
  Reg : ∀ k, Set (Y k)

/-- The resampled density `R̂ ρ k`. -/
def M1Data.rhat (P : M1Data X Y) (k : ℕ) : X k → ℝ≥0∞ :=
  resample (P.φ k) (P.ρ k) (P.w k) (P.N k) (P.D k) (P.Reg k)

/-- **The named hypotheses of M1.** -/
structure M1Hypotheses (P : M1Data X Y) (μ0 : Measure (X 0)) (Form : ∀ k, (X k → ℝ≥0∞) → Prop) : Prop where
  meas_φ : ∀ k, Measurable (P.φ k)
  meas_ψ : ∀ k, Measurable (P.ψ k)
  meas_ρ : ∀ k, Measurable (P.ρ k)
  meas_w : ∀ k, Measurable (P.w k)
  meas_N : ∀ k, Measurable (P.N k)
  meas_D : ∀ k, Measurable (P.D k)
  meas_Reg : ∀ k, MeasurableSet (P.Reg k)
  factor : ∀ k, P.B k = P.ψ k ∘ P.φ k
  fibreN : ∀ k, ((P.ν k).withDensity (P.ρ k)).map (P.φ k) = (P.lam k).withDensity (P.N k)
  fibreD : ∀ k, ((P.ν k).withDensity (P.w k)).map (P.φ k) = (P.lam k).withDensity (P.D k)
  D_ne_zero : ∀ k, ∀ y ∈ P.Reg k, P.D k y ≠ 0
  D_ne_top : ∀ k, ∀ y ∈ P.Reg k, P.D k y ≠ ∞
  nextDensity : ∀ k, ((P.ν k).withDensity (P.rhat k)).map (P.B k) = (P.ν (k + 1)).withDensity (P.ρ (k + 1))
  base : (P.ν 0).withDensity (P.ρ 0) = μ0
  form0 : Form 0 (P.ρ 0)
  stepEstimates : ∀ k, Form k (P.ρ k) → Form (k + 1) (P.ρ (k + 1))

/-- **One step is law-preserving:** the pushforward of the resampled term is the pushforward of the term. -/
theorem M1Hypotheses.step_law {P : M1Data X Y} {μ0 : Measure (X 0)} {Form : ∀ k, (X k → ℝ≥0∞) → Prop}
    (H : M1Hypotheses P μ0 Form) (k : ℕ) :
    ((P.ν k).withDensity (P.rhat k)).map (P.B k) = ((P.ν k).withDensity (P.ρ k)).map (P.B k) := by
  rw [H.factor k]
  exact map_comp_resample_eq (P.ν k) (P.lam k) (H.meas_φ k) (H.meas_ψ k) (H.meas_ρ k) (H.meas_w k) (H.meas_N k)
    (H.meas_D k) (H.meas_Reg k) (H.fibreN k) (H.fibreD k) (H.D_ne_zero k) (H.D_ne_top k)

/-- **M1, assembled.** Under the named hypotheses, at every scale the renormalisation-group density has the inductive
form **and is the true law of the block field**. -/
theorem m1_assembly {P : M1Data X Y} {μ0 : Measure (X 0)} {Form : ∀ k, (X k → ℝ≥0∞) → Prop}
    (H : M1Hypotheses P μ0 Form) (k : ℕ) :
    Form k (P.ρ k) ∧ (P.ν k).withDensity (P.ρ k) = trueLaw P.B μ0 k := by
  induction k with
  | zero => exact ⟨H.form0, H.base⟩
  | succ k ih =>
    refine ⟨H.stepEstimates k ih.1, ?_⟩
    rw [← H.nextDensity k, H.step_law k, ih.2]
    rfl

/-- **The law half needs none of the estimates.** -/
theorem m1_laws {P : M1Data X Y} {μ0 : Measure (X 0)} {Form : ∀ k, (X k → ℝ≥0∞) → Prop}
    (H : M1Hypotheses P μ0 Form) (k : ℕ) : (P.ν k).withDensity (P.ρ k) = trueLaw P.B μ0 k :=
  (m1_assembly H k).2

/-! ## The step estimates, row by row

`stepEstimates` bundles the estimates of §5-§7 of the paper outline. Here it is split into one named hypothesis per row
of `M1-PLAN.md`, Part B, plus the row S1 that combines them (the paper's assembly of one step) and the external
running-coupling input ([I] Theorem 2). Each row is an abstract statement about scale `k` (its precise content is the
paper's); `m1_assembly_rows` shows that the rows, the combination S1 and the bare form give M1. -/

/-- The statements of the rows (one predicate per scale for each row of `M1-PLAN.md`, Part B). -/
structure M1RowStatements where
  /-- X2: gauge-fixing removal exact inside `T` -/
  X2 : ℕ → Prop
  /-- P1: Balaban's preliminary integrations ([IV] (1.10)-(1.99)) -/
  P1 : ℕ → Prop
  /-- P2: restriction `χ_{k,Λ}` and extension of the outside field ([IV] (1.74)-(1.75)) -/
  P2 : ℕ → Prop
  /-- V1: constrained minimiser (`[15]` Thm 1, Prop 9; with excision, `V1-EXCISION.md`) -/
  V1 : ℕ → Prop
  /-- V2: background regularity ([IV] (1.80)-(1.98)) -/
  V2 : ℕ → Prop
  /-- D-mod: moderate cores dilute (`NOTE.md` 2.3, `Dilution.lean`) -/
  Dmod : ℕ → Prop
  /-- TRAP: deep cores trapped at creation and excised (`TRAP.md`, `TRAP-CHECKS.md`) -/
  TRAP : ℕ → Prop
  /-- P2′: subscale hole decoupling (`P2-PRIME.md`) -/
  P2prime : ℕ → Prop
  /-- P4: root suppression of a deep core -/
  P4 : ℕ → Prop
  /-- E1: linear term (identity) -/
  E1 : ℕ → Prop
  /-- E2: quadratic form positive on the constrained subspace -/
  E2 : ℕ → Prop
  /-- E3: denominator and Wilson-term cancellation (`E3.md`, `POINCARE.md`) -/
  E3 : ℕ → Prop
  /-- E4: localisation of the `W`-dependence -/
  E4 : ℕ → Prop
  /-- E5: matched normalisations -/
  E5 : ℕ → Prop
  /-- E6: analytic extension -/
  E6 : ℕ → Prop
  /-- E7: large-field factors under δ-constraints -/
  E7 : ℕ → Prop
  /-- E7.J: fibre mass (`E7J.md`, `FibreMass.lean`) -/
  E7J : ℕ → Prop
  /-- E8: entropy induction -/
  E8 : ℕ → Prop
  /-- E9: the fundamental inequality -/
  E9 : ℕ → Prop
  /-- E11: polymer gas -/
  E11 : ℕ → Prop
  /-- E12: exponentiation -/
  E12 : ℕ → Prop
  /-- E13: final form -/
  E13 : ℕ → Prop
  /-- external: the running coupling stays below `γ` ([I] Theorem 2, unpublished proof) -/
  runningCoupling : Prop

/-- **The row hypotheses**: each row holds at every scale, the coupling input holds, and S1 combines them into one step
of the inductive form. -/
structure M1RowHypotheses {X : ℕ → Type u} (R : M1RowStatements) (ρ : ∀ k, X k → ℝ≥0∞)
    (Form : ∀ k, (X k → ℝ≥0∞) → Prop) : Prop where
  x2 : ∀ k, R.X2 k
  p1 : ∀ k, R.P1 k
  p2 : ∀ k, R.P2 k
  v1 : ∀ k, R.V1 k
  v2 : ∀ k, R.V2 k
  dmod : ∀ k, R.Dmod k
  trap : ∀ k, R.TRAP k
  p2prime : ∀ k, R.P2prime k
  p4 : ∀ k, R.P4 k
  e1 : ∀ k, R.E1 k
  e2 : ∀ k, R.E2 k
  e3 : ∀ k, R.E3 k
  e4 : ∀ k, R.E4 k
  e5 : ∀ k, R.E5 k
  e6 : ∀ k, R.E6 k
  e7 : ∀ k, R.E7 k
  e7J : ∀ k, R.E7J k
  e8 : ∀ k, R.E8 k
  e9 : ∀ k, R.E9 k
  e11 : ∀ k, R.E11 k
  e12 : ∀ k, R.E12 k
  e13 : ∀ k, R.E13 k
  coupling : R.runningCoupling
  /-- S1: the paper's assembly of one step from the rows -/
  assemble : ∀ k, R.runningCoupling → R.X2 k → R.P1 k → R.P2 k → R.V1 k → R.V2 k → R.Dmod k → R.TRAP k →
    R.P2prime k → R.P4 k → R.E1 k → R.E2 k → R.E3 k → R.E4 k → R.E5 k → R.E6 k → R.E7 k → R.E7J k → R.E8 k →
    R.E9 k → R.E11 k → R.E12 k → R.E13 k → Form k (ρ k) → Form (k + 1) (ρ (k + 1))

/-- The rows give `stepEstimates`. -/
theorem M1RowHypotheses.stepEstimates {X : ℕ → Type u} {R : M1RowStatements} {ρ : ∀ k, X k → ℝ≥0∞}
    {Form : ∀ k, (X k → ℝ≥0∞) → Prop} (HR : M1RowHypotheses R ρ Form) (k : ℕ) :
    Form k (ρ k) → Form (k + 1) (ρ (k + 1)) :=
  HR.assemble k HR.coupling (HR.x2 k) (HR.p1 k) (HR.p2 k) (HR.v1 k) (HR.v2 k) (HR.dmod k) (HR.trap k)
    (HR.p2prime k) (HR.p4 k) (HR.e1 k) (HR.e2 k) (HR.e3 k) (HR.e4 k) (HR.e5 k) (HR.e6 k) (HR.e7 k) (HR.e7J k)
    (HR.e8 k) (HR.e9 k) (HR.e11 k) (HR.e12 k) (HR.e13 k)

/-- **M1, assembled row by row.** The data hypotheses (with no estimate content: `Form` trivial there), the rows with
their combination S1, and the bare form give, at every scale, the inductive form **and** the identification of the
renormalisation-group density with the true law. -/
theorem m1_assembly_rows {P : M1Data X Y} {μ0 : Measure (X 0)} {Form : ∀ k, (X k → ℝ≥0∞) → Prop}
    (H : M1Hypotheses P μ0 (fun _ _ => True)) (R : M1RowStatements) (HR : M1RowHypotheses R P.ρ Form)
    (h0 : Form 0 (P.ρ 0)) (k : ℕ) :
    Form k (P.ρ k) ∧ (P.ν k).withDensity (P.ρ k) = trueLaw P.B μ0 k := by
  refine ⟨?_, m1_laws H k⟩
  induction k with
  | zero => exact h0
  | succ k ih => exact HR.stepEstimates k ih

end ProofPhase.M1
