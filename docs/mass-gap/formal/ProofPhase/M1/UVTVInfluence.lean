/-
Proof phase, M1 tools (m1-tools), Lean phase, module 7: building `ScaleHyp` from per-block coupling bounds,
smallness and counting (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/PACK-SCALEHYP.md`.
-/

import ProofPhase.M1.UVTVScale

/-!
# `ScaleHyp` from three separated inputs

`ScaleHyp` (module 1) asks for an influence matrix `k b y z` on good blocks and the column condition. This module builds
it from three inputs of different kinds, so that the instantiation can attack them separately:

1. **The block coupling bound** (`hunion`, Balaban's analysis: H3 for good boxes, Lemma C for composite boxes). The
   block coupling leaves **some** site of the block disagreeing with probability at most `Σ_{z ∉ B, σ_z ≠ σ'_z} κ b z`.
   For a maximal coupling this is the total-variation distance of the two block laws. It is the natural output of a
   density-ratio estimate.
2. **Smallness** (`hsmall`): `κ b z ≤ ε · w b z`, with `ε` the small parameter: the decay across the collar,
   `e^{-m' w}`, times the constant-size inputs (`UV-TV.md` 29.4).
3. **Counting** (`hcount`, pure geometry): `Σ_{b good, z ∉ B b} Σ_{y ∈ B b} w b z e^{λ d(z, y)} ≤ M c(z)`.

`ScaleHyp.ofBlockBounds` returns a `ScaleHyp` with `k b y z = κ b z` and `γ = ε M`, so it needs `ε M < 1`.

What stays paper: the block coupling bound itself, i.e. `hunion`, with `κ` given by the density-ratio estimate of the
box law in its boundary data (`UV-TV.md` 29.2-29.5, 33.4). See `PACK-SCALEHYP.md`.
-/

open MeasureTheory ProbabilityTheory Finset ProofPhase.OneBox ProofPhase.OneBox.CouplingSpec

open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.M1.UVTV

variable {ι S β : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] [Fintype β] [DecidableEq β]

/-- One site's disagreement is bounded by the block's "differs somewhere" event. -/
theorem real_disagree_le_differOn {π : Measure ((ι → S) × (ι → S))} [IsFiniteMeasure π] {B : Finset ι} {y : ι}
    (hy : y ∈ B) : π.real (disagree (S := S) y) ≤ π.real (differOn B) :=
  measureReal_mono (Set.subset_biUnion_of_mem (u := fun x => disagree (S := S) x) hy)

/-- **`ScaleHyp` from a block coupling bound, smallness and counting.** -/
def ScaleHyp.ofBlockBounds {μ μ' : Measure (ι → S)} (C : CouplingSpec μ μ' β)
    (dist : ι → ι → ℝ) (dist_self : ∀ x, dist x x = 0) (dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (good : Finset β) (κ w : β → ι → ℝ) (hκ : ∀ b z, 0 ≤ κ b z) (lam : ℝ) (hlam : 0 ≤ lam)
    (ε M cmin : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hεM : ε * M < 1) (hcmin : 0 < cmin)
    (hcmin_le : ∀ x, cmin ≤ coverage C.B x)
    (hunion : ∀ b ∈ good, ∀ σ ∈ C.Ω₀, ∀ σ' ∈ C.Ω₀',
      (C.Q b (σ, σ')).real (differOn (C.B b)) ≤
        ∑ z ∈ (C.B b)ᶜ, (disagree z).indicator (fun _ => κ b z) (σ, σ'))
    (hsmall : ∀ b z, κ b z ≤ ε * w b z)
    (hcount : ∀ z, ∑ b ∈ good.filter (fun b => z ∉ C.B b), ∑ y ∈ C.B b, w b z * Real.exp (lam * dist z y) ≤
      M * coverage C.B z) :
    ScaleHyp μ μ' β where
  C := C
  dist := dist
  dist_self := dist_self
  dist_triangle := dist_triangle
  good := good
  k := fun b _ z => κ b z
  k_nonneg := fun b _ z => hκ b z
  lam := lam
  lam_nonneg := hlam
  γ := ε * M
  cmin := cmin
  γ_nonneg := mul_nonneg hε hM
  γ_lt_one := hεM
  cmin_pos := hcmin
  cmin_le := hcmin_le
  influence := fun b hb σ hσ σ' hσ' y hy =>
    (real_disagree_le_differOn hy).trans (hunion b hb σ hσ σ' hσ')
  column := fun z => by
    calc ∑ b ∈ good.filter (fun b => z ∉ C.B b), ∑ y ∈ C.B b, κ b z * Real.exp (lam * dist z y)
        ≤ ∑ b ∈ good.filter (fun b => z ∉ C.B b), ∑ y ∈ C.B b, ε * (w b z * Real.exp (lam * dist z y)) := by
          refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun y _ => ?_
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hsmall b z) (Real.exp_pos _).le
      _ = ε * ∑ b ∈ good.filter (fun b => z ∉ C.B b), ∑ y ∈ C.B b, w b z * Real.exp (lam * dist z y) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
      _ ≤ ε * (M * coverage C.B z) := mul_le_mul_of_nonneg_left (hcount z) hε
      _ = ε * M * coverage C.B z := by ring

end ProofPhase.M1.UVTV
