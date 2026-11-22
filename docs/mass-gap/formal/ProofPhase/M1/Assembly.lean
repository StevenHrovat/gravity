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

**Claim level.** `m1_assembly` is proved (standard axioms). It makes the logical structure of M1 machine-checked: the
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

end ProofPhase.M1
