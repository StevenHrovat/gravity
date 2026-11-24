/-
Proof phase, ScaleHyp kit, module 2: the maximal coupling as a measurable kernel (2026-11-23).
Released under Apache 2.0.

Pack: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/PACK-SCALEHYP.md`, item (b).
Note: `docs/mass-gap/weak-coupling/proof-phase/scalehyp/NOTE.md`.
-/

import ProofPhase.ScaleHyp.MaxCoupling

/-!
# The maximal coupling as a kernel

Densities `ρ x a`, `ρ' x a` that are jointly measurable in the parameter `x` and the point `a`, against one s-finite
reference measure `Λ` (`UV-TV.md` 38.5 (3): "each piece is measurable in `(σ, σ')` by Tonelli").

* `mapParam K g`: the push-forward of a kernel `K` by a map `g x` that depends measurably on the parameter,
  `x ↦ (K x).map (g x)`. It is `(id ×ₖ K).map (uncurry g)`.
* `measurable_maxCoupling`: for jointly measurable probability densities, `x ↦ maxCoupling Λ (ρ x) (ρ' x)` is
  measurable. The proof writes both pieces through `Kernel.const`, `Kernel.withDensity`, `Kernel.map` and `×ₖ`; the
  density kernels have mass at most `1`, so they are finite kernels and `×ₖ` applies.
* `maxCouplingKernel Λ ρ ρ'`: that family as a `Kernel`.
* `maxCouplingKernel_apply`: at every `x` it is `maxCoupling Λ (ρ x) (ρ' x)`, so every property of module 1 holds
  pointwise.
* `isMarkovKernel_maxCouplingKernel`: it is a Markov kernel when every `ρ x Λ`, `ρ' x Λ` is a probability measure.
-/

open MeasureTheory ProbabilityTheory Set Function

open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.ScaleHypKit

variable {X α A Y : Type*} [MeasurableSpace X] [MeasurableSpace α] [MeasurableSpace A] [MeasurableSpace Y]

/-! ### Push-forward by a parameter-dependent map -/

/-- The kernel `x ↦ (K x).map (g x)`. -/
def mapParam (K : Kernel X A) (g : X → A → Y) : Kernel X Y :=
  (Kernel.id ×ₖ K).map (fun p => g p.1 p.2)

theorem mapParam_apply (K : Kernel X A) [IsSFiniteKernel K] {g : X → A → Y} (hg : Measurable (uncurry g))
    (x : X) : mapParam K g x = (K x).map (g x) := by
  have hg' : Measurable fun p : X × A => g p.1 p.2 := hg
  rw [mapParam, Kernel.map_apply _ hg', Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map hg' measurable_prodMk_left]
  rfl

theorem isMarkovKernel_mapParam (K : Kernel X A) [IsMarkovKernel K] {g : X → A → Y}
    (hg : Measurable (uncurry g)) : IsMarkovKernel (mapParam K g) :=
  ⟨fun x => by
    rw [mapParam_apply K hg]
    exact (Measure.isProbabilityMeasure_map_iff (hg.comp measurable_prodMk_left).aemeasurable).mpr inferInstance⟩

/-! ### The maximal coupling kernel -/

variable {Λ : Measure α} {ρ ρ' : X → α → ℝ≥0∞}

theorem measurable_overlap [SFinite Λ] (hρ : Measurable (uncurry ρ)) (hρ' : Measurable (uncurry ρ')) :
    Measurable fun x => overlap Λ (ρ x) (ρ' x) :=
  Measurable.lintegral_prod_right' (ν := Λ) (f := fun p => min (ρ p.1 p.2) (ρ' p.1 p.2)) (hρ.min hρ')

/-- A density kernel of total mass at most `1` is a finite kernel. -/
theorem isFiniteKernel_withDensity_const [SFinite Λ] {f : X → α → ℝ≥0∞} (hf : Measurable (uncurry f))
    (hle : ∀ x, ∫⁻ a, f x a ∂Λ ≤ 1) : IsFiniteKernel (Kernel.withDensity (Kernel.const X Λ) f) :=
  ⟨⟨1, ENNReal.one_lt_top, fun x => by
    rw [Kernel.withDensity_apply' _ hf, Kernel.const_apply, Measure.restrict_univ]; exact hle x⟩⟩

/-- **Measurability of the maximal coupling in the parameter**, for jointly measurable probability densities. The
two pieces are the kernels `(const Λ).withDensity (ρ ∧ ρ')` mapped to the diagonal and the product kernel
`(const Λ).withDensity (ρ - ρ ∧ ρ') ×ₖ (const Λ).withDensity (ρ' - ρ ∧ ρ')` (finite kernels, of mass at most `1`); the
factor `(1 - ∫ ρ ∧ ρ')⁻¹` is a measurable function of the parameter by Tonelli. -/
theorem measurable_maxCoupling [SFinite Λ] (hρ : Measurable (uncurry ρ)) (hρ' : Measurable (uncurry ρ'))
    (h1 : ∀ x, ∫⁻ a, ρ x a ∂Λ = 1) (h1' : ∀ x, ∫⁻ a, ρ' x a ∂Λ = 1) :
    Measurable fun x => maxCoupling Λ (ρ x) (ρ' x) := by
  have hmin : Measurable (uncurry fun x a => min (ρ x a) (ρ' x a)) := hρ.min hρ'
  have he : Measurable (uncurry fun x => excess (ρ x) (ρ' x)) := hρ.sub (hρ.min hρ')
  have he' : Measurable (uncurry fun x => excess (ρ' x) (ρ x)) := hρ'.sub (hρ'.min hρ)
  have hx : ∀ x, Measurable (ρ x) := fun x => hρ.comp measurable_prodMk_left
  have hx' : ∀ x, Measurable (ρ' x) := fun x => hρ'.comp measurable_prodMk_left
  have : IsFiniteKernel (Kernel.withDensity (Kernel.const X Λ) fun x a => min (ρ x a) (ρ' x a)) :=
    isFiniteKernel_withDensity_const hmin fun x => overlap_le (h1 x)
  have : IsFiniteKernel (Kernel.withDensity (Kernel.const X Λ) fun x => excess (ρ x) (ρ' x)) :=
    isFiniteKernel_withDensity_const he fun x => (lintegral_excess (hx x) (hx' x) (h1 x)).le.trans tsub_le_self
  have : IsFiniteKernel (Kernel.withDensity (Kernel.const X Λ) fun x => excess (ρ' x) (ρ x)) :=
    isFiniteKernel_withDensity_const he' fun x =>
      (lintegral_excess' (hx x) (hx' x) (h1' x)).le.trans tsub_le_self
  set D := (Kernel.withDensity (Kernel.const X Λ) fun x a => min (ρ x a) (ρ' x a)).map (fun a => (a, a))
    with hDdef
  set P := Kernel.withDensity (Kernel.const X Λ) (fun x => excess (ρ x) (ρ' x)) ×ₖ
    Kernel.withDensity (Kernel.const X Λ) (fun x => excess (ρ' x) (ρ x)) with hPdef
  have hD : ∀ x, D x = (Λ.withDensity fun a => min (ρ x a) (ρ' x a)).map (fun a => (a, a)) := fun x => by
    rw [hDdef, Kernel.map_apply _ measurable_diag, Kernel.withDensity_apply _ hmin, Kernel.const_apply]
  have hP : ∀ x, P x = (Λ.withDensity (excess (ρ x) (ρ' x))).prod (Λ.withDensity (excess (ρ' x) (ρ x))) :=
    fun x => by
      rw [hPdef, Kernel.prod_apply, Kernel.withDensity_apply _ he, Kernel.withDensity_apply _ he',
        Kernel.const_apply]
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have heq : (fun x => maxCoupling Λ (ρ x) (ρ' x) s) =
      fun x => D x s + (1 - overlap Λ (ρ x) (ρ' x))⁻¹ * P x s := by
    funext x
    rw [hD, hP, maxCoupling, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [heq]
  exact (Kernel.measurable_coe D hs).add
    (((measurable_const.sub (measurable_overlap hρ hρ')).inv).mul (Kernel.measurable_coe P hs))

open Classical in
/-- **The maximal coupling as a kernel** in the parameter `x`: `x ↦ maxCoupling Λ (ρ x) (ρ' x)` when the densities
are jointly measurable probability densities (and the zero kernel otherwise, never used). -/
def maxCouplingKernel (Λ : Measure α) [SFinite Λ] (ρ ρ' : X → α → ℝ≥0∞) : Kernel X (α × α) :=
  if h : Measurable (uncurry ρ) ∧ Measurable (uncurry ρ') ∧ (∀ x, ∫⁻ a, ρ x a ∂Λ = 1) ∧
      ∀ x, ∫⁻ a, ρ' x a ∂Λ = 1 then
    ⟨fun x => maxCoupling Λ (ρ x) (ρ' x), measurable_maxCoupling h.1 h.2.1 h.2.2.1 h.2.2.2⟩
  else 0

theorem maxCouplingKernel_apply [SFinite Λ] (hρ : Measurable (uncurry ρ)) (hρ' : Measurable (uncurry ρ'))
    (h1 : ∀ x, ∫⁻ a, ρ x a ∂Λ = 1) (h1' : ∀ x, ∫⁻ a, ρ' x a ∂Λ = 1) (x : X) :
    maxCouplingKernel Λ ρ ρ' x = maxCoupling Λ (ρ x) (ρ' x) := by
  unfold maxCouplingKernel
  split_ifs with h
  · rfl
  · exact absurd ⟨hρ, hρ', h1, h1'⟩ h

theorem isMarkovKernel_maxCouplingKernel [SFinite Λ] (hρ : Measurable (uncurry ρ))
    (hρ' : Measurable (uncurry ρ')) (h1 : ∀ x, ∫⁻ a, ρ x a ∂Λ = 1) (h1' : ∀ x, ∫⁻ a, ρ' x a ∂Λ = 1) :
    IsMarkovKernel (maxCouplingKernel Λ ρ ρ') :=
  ⟨fun x => by
    rw [maxCouplingKernel_apply hρ hρ' h1 h1' x]
    exact isProbabilityMeasure_maxCoupling (hρ.comp measurable_prodMk_left) (hρ'.comp measurable_prodMk_left)
      (h1 x) (h1' x)⟩

end ProofPhase.ScaleHypKit
