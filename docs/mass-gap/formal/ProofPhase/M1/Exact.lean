/-
Proof phase, M1 tools (m1-tools): exactness of the block-constrained large-field step (2026-11-22). Released under
Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/NOTE.md`, section 3.
-/

import Mathlib

/-!
# The conditional R step preserves the law of the next block field

Setting (`c6f-m1scope/ONE-STEP.md` 2.1). One term of the effective density is a measure `ν.withDensity I` on the
current field `x : α` (the field `V_k` on the renormalisation domain `Λ` together with everything else the term
depends on). The next renormalisation step `T` is a pushforward by the blocking map; we only use that the blocking
**factors through** a measurable map `φ : α → γ` (in M1: `φ x = (W, V_out)`, the next block field over `Λ` and the
current field outside `Λ`; the full next block field is `ψ ∘ φ`). The step `R̂` replaces the density `I` by

  `R̂ I (x) = ŵ x · N(φ x) / D(φ x)` where `φ x ∈ Reg`, and leaves `I x` unchanged elsewhere,

with `ŵ` the reference (small-field) kernel, `N` and `D` the fibre integrals of `I` and `ŵ` (the δ-function
integrals `N(W) = ∫ dV δ(V̄ W⁻¹) I(V)`, `D(W) = ∫ dV δ(V̄ W⁻¹) ŵ(V)`, written measure-theoretically as densities of
the pushforwards against a reference measure `λ` on `γ`), and `Reg` the regular set of the next field (branch (b));
off `Reg` (branch (a)) the term is left unrenormalised.

* **`map_resample_eq`** (proved): if `N`, `D` represent the two pushforwards and `0 < D < ∞` on `Reg`, then
  `φ_*(ν.withDensity (R̂ I)) = φ_*(ν.withDensity I)`: the R̂ step leaves the joint law of `(W, V_out)` unchanged.
* **`map_comp_resample_eq`**: hence the law of every function of `φ`, in particular of the next block field
  `ψ ∘ φ` (`T R̂ = T`).
* **`map_resample_rnDeriv_eq`**: the intrinsic form, `N/D` replaced by the Radon–Nikodym derivative of the two
  pushforwards; the only hypotheses are finiteness and absolute continuity.
* **`sum_map_resample_eq`**: term by term over a finite history sum.

**Hypotheses, named.** Measurability of `φ, I, ŵ, N, D`; the fibre representation of `N` and `D`; `D ≠ 0` and
`D ≠ ∞` on `Reg`. **Analyticity of `D` is not needed for exactness**: it is needed only for the estimates (M1-PLAN,
rows E-*). The non-vanishing `D(W) > 0` on regular `W` is the one analytic input exactness uses.
-/

open MeasureTheory Measure
open scoped ENNReal

noncomputable section

namespace ProofPhase.M1

variable {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]

open Classical in
/-- **The block-constrained resampling density.** On `φ⁻¹ Reg` (regular next field) the density is the reference
kernel times the ratio `N/D` of the fibre integrals; elsewhere the term is left unchanged. -/
def resample (φ : α → γ) (I w : α → ℝ≥0∞) (N D : γ → ℝ≥0∞) (Reg : Set γ) (x : α) : ℝ≥0∞ :=
  if φ x ∈ Reg then w x * (N (φ x) / D (φ x)) else I x

theorem measurable_resample {φ : α → γ} {I w : α → ℝ≥0∞} {N D : γ → ℝ≥0∞} {Reg : Set γ} (hφ : Measurable φ)
    (hI : Measurable I) (hw : Measurable w) (hN : Measurable N) (hD : Measurable D) (hReg : MeasurableSet Reg) :
    Measurable (resample φ I w N D Reg) := by
  classical
  unfold resample
  exact Measurable.ite (hφ hReg) (hw.mul ((hN.comp hφ).div (hD.comp hφ))) hI

/-- **Exactness of the conditional step (ratio form).** If `N` and `D` are the densities (against `λ`) of the
pushforwards under `φ` of the term and of the reference kernel, and `0 < D < ∞` on the regular set, then the
resampled term has the same pushforward under `φ` as the original term. -/
theorem map_resample_eq (ν : Measure α) (lam : Measure γ) {φ : α → γ} {I w : α → ℝ≥0∞} {N D : γ → ℝ≥0∞}
    {Reg : Set γ} (hφ : Measurable φ) (hI : Measurable I) (hw : Measurable w) (hN : Measurable N)
    (hD : Measurable D) (hReg : MeasurableSet Reg)
    (hNrep : (ν.withDensity I).map φ = lam.withDensity N)
    (hDrep : (ν.withDensity w).map φ = lam.withDensity D)
    (hD0 : ∀ y ∈ Reg, D y ≠ 0) (hDtop : ∀ y ∈ Reg, D y ≠ ∞) :
    (ν.withDensity (resample φ I w N D Reg)).map φ = (ν.withDensity I).map φ := by
  classical
  have hR := measurable_resample hφ hI hw hN hD hReg
  ext A hA
  rw [map_apply hφ hA, map_apply hφ hA, withDensity_apply _ (hφ hA), withDensity_apply _ (hφ hA)]
  have hS : MeasurableSet (φ ⁻¹' Reg) := hφ hReg
  rw [← lintegral_inter_add_sdiff _ (φ ⁻¹' A) hS, ← lintegral_inter_add_sdiff (fun x => I x) (φ ⁻¹' A) hS]
  congr 1
  · -- branch (b): the regular part
    have hset : φ ⁻¹' A ∩ φ ⁻¹' Reg = φ ⁻¹' (A ∩ Reg) := rfl
    have hAR : MeasurableSet (A ∩ Reg) := hA.inter hReg
    have hg : Measurable (fun y => N y / D y) := hN.div hD
    calc ∫⁻ x in φ ⁻¹' A ∩ φ ⁻¹' Reg, resample φ I w N D Reg x ∂ν
        = ∫⁻ x in φ ⁻¹' (A ∩ Reg), (w * fun x => N (φ x) / D (φ x)) x ∂ν := by
          rw [hset]
          refine setLIntegral_congr_fun (hφ hAR) (fun x hx => ?_)
          simp [resample, hx.2]
      _ = ∫⁻ x in φ ⁻¹' (A ∩ Reg), N (φ x) / D (φ x) ∂(ν.withDensity w) :=
          (setLIntegral_withDensity_eq_setLIntegral_mul ν hw (hg.comp hφ) (hφ hAR)).symm
      _ = ∫⁻ y in A ∩ Reg, N y / D y ∂((ν.withDensity w).map φ) :=
          (setLIntegral_map hAR hg hφ).symm
      _ = ∫⁻ y in A ∩ Reg, (D * fun y => N y / D y) y ∂lam := by
          rw [hDrep, setLIntegral_withDensity_eq_setLIntegral_mul lam hD hg hAR]
      _ = ∫⁻ y in A ∩ Reg, N y ∂lam := by
          refine setLIntegral_congr_fun hAR (fun y hy => ?_)
          simp only [Pi.mul_apply]
          exact ENNReal.mul_div_cancel (hD0 y hy.2) (hDtop y hy.2)
      _ = (ν.withDensity I).map φ (A ∩ Reg) := by
          rw [hNrep, withDensity_apply _ hAR]
      _ = ∫⁻ x in φ ⁻¹' A ∩ φ ⁻¹' Reg, I x ∂ν := by
          rw [map_apply hφ hAR, withDensity_apply _ (hφ hAR), hset]
  · -- branch (a): left unchanged
    refine setLIntegral_congr_fun ((hφ hA).diff hS) (fun x hx => ?_)
    have hx2 : φ x ∉ Reg := hx.2
    simp [resample, hx2]

/-- **`T R̂ = T`.** The resampled term and the original term have the same law under every measurable function of
`φ`, in particular under the next blocking `ψ ∘ φ`. -/
theorem map_comp_resample_eq {δ : Type*} [MeasurableSpace δ] (ν : Measure α) (lam : Measure γ) {φ : α → γ}
    {ψ : γ → δ} {I w : α → ℝ≥0∞} {N D : γ → ℝ≥0∞} {Reg : Set γ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hI : Measurable I) (hw : Measurable w) (hN : Measurable N) (hD : Measurable D) (hReg : MeasurableSet Reg)
    (hNrep : (ν.withDensity I).map φ = lam.withDensity N)
    (hDrep : (ν.withDensity w).map φ = lam.withDensity D)
    (hD0 : ∀ y ∈ Reg, D y ≠ 0) (hDtop : ∀ y ∈ Reg, D y ≠ ∞) :
    (ν.withDensity (resample φ I w N D Reg)).map (ψ ∘ φ) = (ν.withDensity I).map (ψ ∘ φ) := by
  rw [← map_map hψ hφ, ← map_map hψ hφ,
    map_resample_eq ν lam hφ hI hw hN hD hReg hNrep hDrep hD0 hDtop]

/-- **Exactness, intrinsic form.** With finite term and reference measures and the pushforward of the term
absolutely continuous with respect to that of the reference kernel, resampling with the Radon–Nikodym ratio preserves
the pushforward. No fibre densities, no regular set: the ratio `N/D` is `d(φ_* I)/d(φ_* ŵ)`. -/
theorem map_resample_rnDeriv_eq (ν : Measure α) {φ : α → γ} {I w : α → ℝ≥0∞} (hφ : Measurable φ)
    (hI : Measurable I) (hw : Measurable w) [IsFiniteMeasure (ν.withDensity I)]
    [IsFiniteMeasure (ν.withDensity w)]
    (hac : (ν.withDensity I).map φ ≪ (ν.withDensity w).map φ) :
    (ν.withDensity (fun x => w x * ((ν.withDensity I).map φ).rnDeriv ((ν.withDensity w).map φ) (φ x))).map φ
      = (ν.withDensity I).map φ := by
  set ρ := (ν.withDensity w).map φ
  set N := ((ν.withDensity I).map φ).rnDeriv ρ
  have h := map_resample_eq ν ρ (N := N) (D := fun _ => 1) (Reg := Set.univ) hφ hI hw
    (measurable_rnDeriv _ _) measurable_const MeasurableSet.univ
    (withDensity_rnDeriv_eq _ _ hac).symm (by simp [ρ]) (fun _ _ => one_ne_zero)
    (fun _ _ => ENNReal.one_ne_top)
  have hfun : resample φ I w N (fun _ => 1) Set.univ = fun x => w x * N (φ x) := by
    funext x; simp [resample]
  rw [← hfun]
  exact h

/-- **Term by term.** For a finite family of terms (the history sum of the effective density), each resampled with
its own fibre data, the pushforward of the sum is unchanged. -/
theorem sum_map_resample_eq {τ : Type*} (s : Finset τ) (ν : Measure α) (lam : Measure γ) {φ : α → γ}
    {I w : τ → α → ℝ≥0∞} {N D : τ → γ → ℝ≥0∞} {Reg : τ → Set γ} (hφ : Measurable φ)
    (hI : ∀ t, Measurable (I t)) (hw : ∀ t, Measurable (w t)) (hN : ∀ t, Measurable (N t))
    (hD : ∀ t, Measurable (D t)) (hReg : ∀ t, MeasurableSet (Reg t))
    (hNrep : ∀ t, (ν.withDensity (I t)).map φ = lam.withDensity (N t))
    (hDrep : ∀ t, (ν.withDensity (w t)).map φ = lam.withDensity (D t))
    (hD0 : ∀ t, ∀ y ∈ Reg t, D t y ≠ 0) (hDtop : ∀ t, ∀ y ∈ Reg t, D t y ≠ ∞) :
    (∑ t ∈ s, ν.withDensity (resample φ (I t) (w t) (N t) (D t) (Reg t))).map φ
      = (∑ t ∈ s, ν.withDensity (I t)).map φ := by
  rw [Measure.map_finset_sum hφ.aemeasurable, Measure.map_finset_sum hφ.aemeasurable]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  exact map_resample_eq ν lam hφ (hI t) (hw t) (hN t) (hD t) (hReg t) (hNrep t) (hDrep t) (hD0 t) (hDtop t)

end ProofPhase.M1
