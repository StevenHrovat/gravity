/-
Proof phase, cycle 9, workstream c9b (the adjoint half gamma_A of the split one-box criterion): generic comparison
lemmas (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/NOTE.md`, sections 2 and 5.
-/

import Mathlib

/-!
# Transferring influence bounds between two specifications

Everything here is generic (no gauge or lattice content); it is the measure-theoretic core of route (a) of the note:
"the true conditional law is the fitted law tilted by a residual; bound the influence of the true law by the fitted
influence plus a norm of the residual that itself bounds influences".

**Tilts.** For a probability measure `ν` and a bounded log-weight `f`, `tiltAvg ν f F = ∫ F e^f dν / ∫ e^f dν` is the
average of `F` under the Gibbs law `e^f ν / Z`. A single-site (or box) conditional law of a finite-volume Gibbs measure
with positive density is of this form, with `f` the conditional log-density (`H_σ`, depending on the boundary `σ`).

* `abs_tiltAvg_add_sub_le` (**tilt lemma**): if the change `g` of the log-weight has oscillation `≤ δ` and
  `|F - c| ≤ M`, the two averages differ by at most `M (e^δ - 1)`. With `g = H_{σ'} - H_σ` this is the sup-form
  influence bound by the **mixed variation** `osc_ξ (H_{σ'}(ξ) - H_σ(ξ))`.
* `abs_tiltAvg_transfer` (**transfer**): if the change splits as `g₁ + g₂` (fitted change plus residual change) with
  oscillations `δ₁, δ₂`, the bound is `M (e^{δ₁+δ₂} - 1) = M (e^{δ₁} - 1) + M e^{δ₁} (e^{δ₂} - 1)`
  (`exp_add_sub_one`): fitted influence plus a residual term controlled by the residual's mixed variation alone.
* `sum_exp_sub_one_le`, `column_lt_one_of_mix`, `residual_budget`: the column form. If every pair coefficient is
  `≤ (e^{m_z} - 1)/2` (the tilt lemma with `M = 1/2`, i.e. test functions of oscillation `≤ 1`) and the mixed
  variations sum to `< log 3`, the Dobrushin column is `< 1`. A fitted mixed column `m̃` leaves the residual the budget
  `log 3 - m̃`.
* `split_tilt` (**the potential hybrid**): for the split influence of `Saturation/Reduction.lean`, the hybrid law
  `r = tilt by H_σ + Δ⁰` (centre-blind part of the boundary change applied, centre-odd part not) gives
  `|q_σ F - r F| ≤ M (e^{δ⁰} - 1)` and `|r F - q_{σ'} F| ≤ M (e^{δ¹} - 1)`.
* `centreBar`, `delta0`, `delta1` and their facts: the centre-blind / centre-odd split of a boundary change through one
  outside value `s ↦ H s` under a central involution `c` (`c (c s) = s`): `delta0` vanishes for a pure centre flip
  (`delta0_centre_flip`) and for centre-odd weights (`delta0_eq_zero_of_odd`, the photon unit test), `delta1`
  vanishes for centre-even weights (`delta1_eq_zero_of_even`), and `delta0` does not see the centre part of the new
  value (`delta0_centre_blind`).

**Mixtures** (`abs_integral_bind_sub_le`): if two laws are mixtures of kernels `K, K'` over the **same** mixing law
`μ` (the centre law, in the layer form of the split), the difference of averages is at most `ε + 2 M μ(Gᶜ)`, where `ε`
bounds the per-component difference on a measurable good set `G`. So the adjoint influence needs a bound only on
centre configurations that are typical under the actual conditional centre law, not uniformly over all of them.
-/

open MeasureTheory ProbabilityTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Adjoint2

/-! ## 1. Tilts and the tilt lemma -/

section Tilt

variable {α : Type*} [MeasurableSpace α]

/-- The partition function of the tilt of `ν` by `e^f`. -/
def tiltZ (ν : Measure α) (f : α → ℝ) : ℝ := ∫ x, Real.exp (f x) ∂ν

/-- The tilted average `E_f[F] = ∫ F e^f dν / ∫ e^f dν`. -/
def tiltAvg (ν : Measure α) (f F : α → ℝ) : ℝ := (∫ x, F x * Real.exp (f x) ∂ν) / tiltZ ν f

theorem integrable_of_abs_le {ν : Measure α} [IsFiniteMeasure ν] {h : α → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) : Integrable h ν :=
  Integrable.of_bound (C := C) hh.aestronglyMeasurable (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem abs_exp_le_of_abs_le {f : α → ℝ} {B : ℝ} (hfB : ∀ x, |f x| ≤ B) (x : α) : |Real.exp (f x)| ≤ Real.exp B := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hfB x))

/-- The tilt of a probability measure by a bounded log-weight has a positive partition function. -/
theorem tiltZ_pos {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ} (hf : Measurable f) {B : ℝ}
    (hfB : ∀ x, |f x| ≤ B) : 0 < tiltZ ν f := by
  have iE : Integrable (fun x => Real.exp (f x)) ν := integrable_of_abs_le hf.exp (abs_exp_le_of_abs_le hfB)
  have h : ∫ _x, Real.exp (-B) ∂ν ≤ tiltZ ν f :=
    integral_mono (integrable_const _) iE fun x => Real.exp_le_exp.mpr (by
      have := hfB x; rw [abs_le] at this; linarith)
  have h1 : ∫ _x, Real.exp (-B) ∂ν = Real.exp (-B) := by simp
  rw [h1] at h
  exact lt_of_lt_of_le (Real.exp_pos _) h

/-- Shifting the test function by a constant shifts the tilted average by the same constant. -/
theorem tiltAvg_sub_const {ν : Measure α} [IsProbabilityMeasure ν] {f F : α → ℝ} (hf : Measurable f)
    (hF : Measurable F) {B M : ℝ} (hfB : ∀ x, |f x| ≤ B) (hFM : ∀ x, |F x| ≤ M) (c : ℝ) :
    tiltAvg ν f (fun x => F x - c) = tiltAvg ν f F - c := by
  have hZ := tiltZ_pos (ν := ν) hf hfB
  have iE : Integrable (fun x => Real.exp (f x)) ν := integrable_of_abs_le hf.exp (abs_exp_le_of_abs_le hfB)
  have iFE : Integrable (fun x => F x * Real.exp (f x)) ν :=
    integrable_of_abs_le (hF.mul hf.exp) fun x => by
      rw [abs_mul]
      exact mul_le_mul (hFM x) (abs_exp_le_of_abs_le hfB x) (abs_nonneg _) ((abs_nonneg _).trans (hFM x))
  unfold tiltAvg
  have e : (fun x => (F x - c) * Real.exp (f x)) = fun x => F x * Real.exp (f x) - c * Real.exp (f x) := by
    funext x; ring
  rw [e, integral_sub iFE (iE.const_mul c), integral_const_mul]
  unfold tiltZ at hZ ⊢
  field_simp

/-- **The tilt lemma, centred form.** If the change `g` of a bounded log-weight `f` has oscillation `≤ δ`
(`a ≤ g ≤ a + δ`) and `|F| ≤ M`, then `|E_{f+g} F - E_f F| ≤ M (e^δ - 1)`. -/
theorem abs_tiltAvg_add_sub_le_of_abs {ν : Measure α} [IsProbabilityMeasure ν] {f g F : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hF : Measurable F) {B a δ M : ℝ} (hfB : ∀ x, |f x| ≤ B)
    (hga : ∀ x, a ≤ g x) (hgδ : ∀ x, g x ≤ a + δ) (hFM : ∀ x, |F x| ≤ M) :
    |tiltAvg ν (fun x => f x + g x) F - tiltAvg ν f F| ≤ M * (Real.exp δ - 1) := by
  obtain ⟨x₀, -⟩ := nonempty_of_measure_ne_zero (μ := ν) (s := Set.univ) (by simp)
  have hδ : 0 ≤ δ := by linarith [hga x₀, hgδ x₀]
  have hM : 0 ≤ M := (abs_nonneg _).trans (hFM x₀)
  -- the pieces
  have hEm : Measurable fun x => Real.exp (f x) := hf.exp
  have hGm : Measurable fun x => Real.exp (g x) := hg.exp
  have hEb := abs_exp_le_of_abs_le hfB
  have hGb : ∀ x, |Real.exp (g x)| ≤ Real.exp (a + δ) := fun x => by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (hgδ x)
  have iE : Integrable (fun x => Real.exp (f x)) ν := integrable_of_abs_le hEm hEb
  have iEG : Integrable (fun x => Real.exp (f x) * Real.exp (g x)) ν :=
    integrable_of_abs_le (hEm.mul hGm) fun x => by
      rw [abs_mul]; exact mul_le_mul (hEb x) (hGb x) (abs_nonneg _) (Real.exp_pos _).le
  have iFE : Integrable (fun x => F x * Real.exp (f x)) ν :=
    integrable_of_abs_le (hF.mul hEm) fun x => by
      rw [abs_mul]; exact mul_le_mul (hFM x) (hEb x) (abs_nonneg _) hM
  have iFEG : Integrable (fun x => F x * Real.exp (f x) * Real.exp (g x)) ν :=
    integrable_of_abs_le ((hF.mul hEm).mul hGm) fun x => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hFM x) (hEb x) (abs_nonneg _) hM) (hGb x) (abs_nonneg _)
        (mul_nonneg hM (Real.exp_pos _).le)
  -- the two partition functions
  have hZ1pos : 0 < ∫ x, Real.exp (f x) ∂ν := tiltZ_pos hf hfB
  have hZ2lo : Real.exp a * ∫ x, Real.exp (f x) ∂ν ≤ ∫ x, Real.exp (f x) * Real.exp (g x) ∂ν := by
    rw [← integral_const_mul]
    exact integral_mono (iE.const_mul _) iEG fun x => by
      show Real.exp a * Real.exp (f x) ≤ Real.exp (f x) * Real.exp (g x)
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hga x)) (Real.exp_pos _).le
  have hZ2hi : ∫ x, Real.exp (f x) * Real.exp (g x) ∂ν ≤ Real.exp (a + δ) * ∫ x, Real.exp (f x) ∂ν := by
    rw [← integral_const_mul]
    exact integral_mono iEG (iE.const_mul _) fun x => by
      show Real.exp (f x) * Real.exp (g x) ≤ Real.exp (a + δ) * Real.exp (f x)
      rw [mul_comm (Real.exp (a + δ))]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hgδ x)) (Real.exp_pos _).le
  generalize hZ1 : ∫ x, Real.exp (f x) ∂ν = Z1 at hZ1pos hZ2lo hZ2hi
  generalize hZ2 : ∫ x, Real.exp (f x) * Real.exp (g x) ∂ν = Z2 at hZ2lo hZ2hi
  have hZ2pos : 0 < Z2 := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hZ1pos) hZ2lo
  -- the relative weight `w = e^g Z1/Z2 ∈ [e^{-δ}, e^δ]`
  set r : ℝ := Z1 / Z2 with hr
  have hr_lo : Real.exp (-(a + δ)) ≤ r := by
    rw [hr, le_div_iff₀ hZ2pos, Real.exp_neg]
    calc (Real.exp (a + δ))⁻¹ * Z2 ≤ (Real.exp (a + δ))⁻¹ * (Real.exp (a + δ) * Z1) :=
          mul_le_mul_of_nonneg_left hZ2hi (inv_nonneg.mpr (Real.exp_pos _).le)
      _ = Z1 := by field_simp
  have hr_hi : r ≤ Real.exp (-a) := by
    rw [hr, div_le_iff₀ hZ2pos, Real.exp_neg]
    calc Z1 = (Real.exp a)⁻¹ * (Real.exp a * Z1) := by field_simp
      _ ≤ (Real.exp a)⁻¹ * Z2 := mul_le_mul_of_nonneg_left hZ2lo (inv_nonneg.mpr (Real.exp_pos _).le)
  have hw_lo : ∀ x, Real.exp (-δ) ≤ Real.exp (g x) * r := fun x => by
    calc Real.exp (-δ) = Real.exp a * Real.exp (-(a + δ)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (g x) * r :=
        mul_le_mul (Real.exp_le_exp.mpr (hga x)) hr_lo (Real.exp_pos _).le (Real.exp_pos _).le
  have hw_hi : ∀ x, Real.exp (g x) * r ≤ Real.exp δ := fun x => by
    calc Real.exp (g x) * r ≤ Real.exp (a + δ) * Real.exp (-a) :=
          mul_le_mul (Real.exp_le_exp.mpr (hgδ x)) hr_hi (le_trans (Real.exp_pos _).le hr_lo)
            (Real.exp_pos _).le
      _ = Real.exp δ := by rw [← Real.exp_add]; ring_nf
  have hsym : 1 - Real.exp (-δ) ≤ Real.exp δ - 1 := by
    have h1 := Real.add_one_le_exp δ
    have h2 := Real.add_one_le_exp (-δ)
    linarith
  have hw : ∀ x, |Real.exp (g x) * r - 1| ≤ Real.exp δ - 1 := fun x => by
    rw [abs_le]; constructor <;> linarith [hw_lo x, hw_hi x]
  -- the key identity
  have hkey : tiltAvg ν (fun x => f x + g x) F - tiltAvg ν f F =
      (∫ x, F x * Real.exp (f x) * (Real.exp (g x) * r - 1) ∂ν) / Z1 := by
    have h1 : ∫ x, F x * Real.exp (f x) * (Real.exp (g x) * r - 1) ∂ν =
        r * ∫ x, F x * Real.exp (f x) * Real.exp (g x) ∂ν - ∫ x, F x * Real.exp (f x) ∂ν := by
      have e : (fun x => F x * Real.exp (f x) * (Real.exp (g x) * r - 1)) =
          fun x => r * (F x * Real.exp (f x) * Real.exp (g x)) - F x * Real.exp (f x) := by
        funext x; ring
      rw [e, integral_sub (iFEG.const_mul r) iFE, integral_const_mul]
    have h2 : (fun x => F x * Real.exp (f x + g x)) = fun x => F x * Real.exp (f x) * Real.exp (g x) := by
      funext x; rw [Real.exp_add]; ring
    have h3 : (fun x => Real.exp (f x + g x)) = fun x => Real.exp (f x) * Real.exp (g x) := by
      funext x; rw [Real.exp_add]
    unfold tiltAvg tiltZ
    rw [h2, h3, h1, hZ1, hZ2, hr]
    field_simp
  -- the bound
  have iD : Integrable (fun x => F x * Real.exp (f x) * (Real.exp (g x) * r - 1)) ν :=
    integrable_of_abs_le ((hF.mul hEm).mul ((hGm.mul_const r).sub_const 1)) fun x => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hFM x) (hEb x) (abs_nonneg _) hM) (hw x) (abs_nonneg _)
        (mul_nonneg hM (Real.exp_pos _).le)
  rw [hkey, abs_div, abs_of_pos hZ1pos, div_le_iff₀ hZ1pos]
  calc |∫ x, F x * Real.exp (f x) * (Real.exp (g x) * r - 1) ∂ν|
      ≤ ∫ x, |F x * Real.exp (f x) * (Real.exp (g x) * r - 1)| ∂ν := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ν)
          (fun x => F x * Real.exp (f x) * (Real.exp (g x) * r - 1))
    _ ≤ ∫ x, M * (Real.exp δ - 1) * Real.exp (f x) ∂ν := by
        refine integral_mono iD.abs (iE.const_mul _) fun x => ?_
        show |F x * Real.exp (f x) * (Real.exp (g x) * r - 1)| ≤ M * (Real.exp δ - 1) * Real.exp (f x)
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos (f x))]
        calc |F x| * Real.exp (f x) * |Real.exp (g x) * r - 1|
            ≤ M * Real.exp (f x) * (Real.exp δ - 1) :=
              mul_le_mul (mul_le_mul_of_nonneg_right (hFM x) (Real.exp_pos _).le) (hw x) (abs_nonneg _)
                (mul_nonneg hM (Real.exp_pos _).le)
          _ = M * (Real.exp δ - 1) * Real.exp (f x) := by ring
    _ = M * (Real.exp δ - 1) * Z1 := by rw [integral_const_mul, hZ1]

/-- **The tilt lemma** (S). If the change `g` of a bounded log-weight has oscillation `≤ δ` and `|F - c| ≤ M`, then
`|E_{f+g} F - E_f F| ≤ M (e^δ - 1)`. With `g = H_{σ'} - H_σ` this bounds the influence of a boundary change by the
mixed variation of the conditional log-density. -/
theorem abs_tiltAvg_add_sub_le {ν : Measure α} [IsProbabilityMeasure ν] {f g F : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hF : Measurable F) {B a δ c M : ℝ} (hfB : ∀ x, |f x| ≤ B)
    (hga : ∀ x, a ≤ g x) (hgδ : ∀ x, g x ≤ a + δ) (hFM : ∀ x, |F x - c| ≤ M) :
    |tiltAvg ν (fun x => f x + g x) F - tiltAvg ν f F| ≤ M * (Real.exp δ - 1) := by
  obtain ⟨x₀, -⟩ := nonempty_of_measure_ne_zero (μ := ν) (s := Set.univ) (by simp)
  have hgB : ∀ x, |f x + g x| ≤ B + (|a| + |δ|) := fun x => by
    have h1 := hfB x; have h2 := hga x; have h3 := hgδ x
    rw [abs_le] at h1 ⊢
    constructor
    · linarith [neg_abs_le a, abs_nonneg δ]
    · linarith [le_abs_self a, le_abs_self δ]
  have hFc : ∀ x, |F x| ≤ M + |c| := fun x => by
    have := hFM x
    calc |F x| = |(F x - c) + c| := by ring_nf
      _ ≤ |F x - c| + |c| := abs_add_le _ _
      _ ≤ M + |c| := by linarith
  have h1 := tiltAvg_sub_const (ν := ν) (f := fun x => f x + g x) (hf.add hg) hF hgB hFc c
  have h2 := tiltAvg_sub_const (ν := ν) hf hF hfB hFc c
  have h3 := abs_tiltAvg_add_sub_le_of_abs (ν := ν) (F := fun x => F x - c) hf hg (hF.sub_const c) hfB hga hgδ hFM
  rw [h1, h2] at h3
  calc |tiltAvg ν (fun x => f x + g x) F - tiltAvg ν f F|
      = |tiltAvg ν (fun x => f x + g x) F - c - (tiltAvg ν f F - c)| := by ring_nf
    _ ≤ M * (Real.exp δ - 1) := h3

/-- `e^{δ₁+δ₂} - 1 = (e^{δ₁} - 1) + e^{δ₁} (e^{δ₂} - 1)`: the fitted part plus the residual part. -/
theorem exp_add_sub_one (δ₁ δ₂ : ℝ) :
    Real.exp (δ₁ + δ₂) - 1 = (Real.exp δ₁ - 1) + Real.exp δ₁ * (Real.exp δ₂ - 1) := by
  rw [Real.exp_add]; ring

/-- **Transfer of an influence bound through a residual** (S). The change of the true log-weight splits as the fitted
change `g₁` (oscillation `≤ δ₁`) plus the residual change `g₂` (oscillation `≤ δ₂`); then the influence is at most
`M (e^{δ₁+δ₂} - 1) = M (e^{δ₁} - 1) + M e^{δ₁} (e^{δ₂} - 1)`. -/
theorem abs_tiltAvg_transfer {ν : Measure α} [IsProbabilityMeasure ν] {f g₁ g₂ F : α → ℝ}
    (hf : Measurable f) (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (hF : Measurable F)
    {B a₁ δ₁ a₂ δ₂ c M : ℝ} (hfB : ∀ x, |f x| ≤ B)
    (h₁a : ∀ x, a₁ ≤ g₁ x) (h₁δ : ∀ x, g₁ x ≤ a₁ + δ₁) (h₂a : ∀ x, a₂ ≤ g₂ x) (h₂δ : ∀ x, g₂ x ≤ a₂ + δ₂)
    (hFM : ∀ x, |F x - c| ≤ M) :
    |tiltAvg ν (fun x => f x + (g₁ x + g₂ x)) F - tiltAvg ν f F| ≤
      M * (Real.exp δ₁ - 1) + M * Real.exp δ₁ * (Real.exp δ₂ - 1) := by
  have h := abs_tiltAvg_add_sub_le (ν := ν) (g := fun x => g₁ x + g₂ x) (a := a₁ + a₂) (δ := δ₁ + δ₂)
    hf (hg₁.add hg₂) hF hfB (fun x => by linarith [h₁a x, h₂a x]) (fun x => by linarith [h₁δ x, h₂δ x]) hFM
  rw [exp_add_sub_one] at h
  linarith

/-- **The potential hybrid of the split** (S). Box laws as tilts: `q_σ = tilt by f`, `q_{σ'} = tilt by f + Δ⁰ + Δ¹`
(`Δ⁰` the centre-blind part of the boundary change, oscillation `≤ δ⁰`; `Δ¹` the centre-odd part, `≤ δ¹`). The hybrid
`r = tilt by f + Δ⁰` sits between them with `|q_σ F - r F| ≤ M (e^{δ⁰} - 1)` (the adjoint part `κ_A`) and
`|r F - q_{σ'} F| ≤ M (e^{δ¹} - 1)` (the centre part `κ_Z`); these are the two hypotheses of
`Saturation.isInfluenceBoundOn_split`. -/
theorem split_tilt {ν : Measure α} [IsProbabilityMeasure ν] {f d0 d1 F : α → ℝ} (hf : Measurable f)
    (h0 : Measurable d0) (h1 : Measurable d1) (hF : Measurable F) {B a0 δ0 a1 δ1 c M : ℝ} (hfB : ∀ x, |f x| ≤ B)
    (h0a : ∀ x, a0 ≤ d0 x) (h0δ : ∀ x, d0 x ≤ a0 + δ0) (h1a : ∀ x, a1 ≤ d1 x) (h1δ : ∀ x, d1 x ≤ a1 + δ1)
    (hFM : ∀ x, |F x - c| ≤ M) :
    |tiltAvg ν f F - tiltAvg ν (fun x => f x + d0 x) F| ≤ M * (Real.exp δ0 - 1) ∧
      |tiltAvg ν (fun x => f x + d0 x) F - tiltAvg ν (fun x => (f x + d0 x) + d1 x) F| ≤
        M * (Real.exp δ1 - 1) := by
  have hfB' : ∀ x, |f x + d0 x| ≤ B + (|a0| + |δ0|) := fun x => by
    have h1 := hfB x; have h2 := h0a x; have h3 := h0δ x
    rw [abs_le] at h1 ⊢
    constructor
    · linarith [neg_abs_le a0, abs_nonneg δ0]
    · linarith [le_abs_self a0, le_abs_self δ0]
  refine ⟨?_, ?_⟩
  · rw [abs_sub_comm]; exact abs_tiltAvg_add_sub_le hf h0 hF hfB h0a h0δ hFM
  · rw [abs_sub_comm]; exact abs_tiltAvg_add_sub_le (hf.add h0) h1 hF hfB' h1a h1δ hFM

end Tilt

/-! ## 2. The column form and the residual budget -/

section Column

variable {ι : Type*}

/-- `Σ (e^{a_i} - 1) ≤ e^{Σ a_i} - 1` for `a_i ≥ 0`. -/
theorem sum_exp_sub_one_le (s : Finset ι) {m : ι → ℝ} (hm : ∀ i ∈ s, 0 ≤ m i) :
    ∑ i ∈ s, (Real.exp (m i) - 1) ≤ Real.exp (∑ i ∈ s, m i) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, sum_insert hj, Real.exp_add]
    have ih' := ih fun i hi => hm i (mem_insert_of_mem hi)
    have hj0 : 1 ≤ Real.exp (m j) := Real.one_le_exp (hm j (mem_insert_self j s))
    have hs0 : 1 ≤ Real.exp (∑ i ∈ s, m i) :=
      Real.one_le_exp (sum_nonneg fun i hi => hm i (mem_insert_of_mem hi))
    nlinarith

/-- **The sup-form Dobrushin column from mixed variations** (S). Pair coefficients `C z ≤ (e^{m z} - 1)/2` (the tilt
lemma for test functions of oscillation `≤ 1`), mixed variations `m z ≥ 0` summing to at most `s < log 3`: the column
is `< 1`. -/
theorem column_lt_one_of_mix (s : Finset ι) {C m : ι → ℝ} (hm : ∀ i ∈ s, 0 ≤ m i)
    (hC : ∀ i ∈ s, C i ≤ (Real.exp (m i) - 1) / 2) {S : ℝ} (hS : ∑ i ∈ s, m i ≤ S) (hS3 : S < Real.log 3) :
    ∑ i ∈ s, C i < 1 := by
  have h1 : ∑ i ∈ s, C i ≤ ∑ i ∈ s, (Real.exp (m i) - 1) / 2 := sum_le_sum hC
  have h2 : ∑ i ∈ s, (Real.exp (m i) - 1) / 2 = (∑ i ∈ s, (Real.exp (m i) - 1)) / 2 := by
    rw [sum_div]
  have h3 := sum_exp_sub_one_le s hm
  have h4 : Real.exp (∑ i ∈ s, m i) < 3 := by
    calc Real.exp (∑ i ∈ s, m i) ≤ Real.exp S := Real.exp_le_exp.mpr hS
      _ < Real.exp (Real.log 3) := Real.exp_lt_exp.mpr hS3
      _ = 3 := Real.exp_log (by norm_num)
  linarith

/-- **The residual budget** (S). If the true mixed variation of each pair is at most the fitted one plus the residual
one (`m z ≤ mfit z + mres z`, subadditivity of the oscillation) and the fitted and residual columns satisfy
`Σ mfit + Σ mres < log 3`, the true sup-form column is `< 1`. -/
theorem residual_budget (s : Finset ι) {C m mfit mres : ι → ℝ} (hm : ∀ i ∈ s, 0 ≤ m i)
    (hC : ∀ i ∈ s, C i ≤ (Real.exp (m i) - 1) / 2) (hsplit : ∀ i ∈ s, m i ≤ mfit i + mres i)
    (hbud : ∑ i ∈ s, mfit i + ∑ i ∈ s, mres i < Real.log 3) : ∑ i ∈ s, C i < 1 := by
  refine column_lt_one_of_mix s hm hC (S := ∑ i ∈ s, mfit i + ∑ i ∈ s, mres i) ?_ hbud
  rw [← sum_add_distrib]
  exact sum_le_sum hsplit

/-- `log 3 > 1.098`: the size of the budget. -/
theorem log_three_gt : (1.098 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have h1 : Real.exp 1.098 = Real.exp 1 * Real.exp 0.098 := by rw [← Real.exp_add]; norm_num
  have h2 : Real.exp 0.098 ≤ 1.1031 := by
    have := Real.exp_bound' (x := (0.098 : ℝ)) (by norm_num) (by norm_num) (n := 3) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  rw [h1]
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.098]

end Column

/-! ## 3. The centre-blind / centre-odd split of a boundary change -/

section CentreSplit

variable {S α : Type*}

/-- The centre average of a weight depending on one outside value: `(H s + H (c s))/2`. -/
def centreBar (c : S → S) (H : S → α → ℝ) (s : S) (x : α) : ℝ := (H s x + H (c s) x) / 2

/-- The centre-blind part of the change `s₀ ↦ s`. -/
def delta0 (c : S → S) (H : S → α → ℝ) (s₀ s : S) (x : α) : ℝ := centreBar c H s x - centreBar c H s₀ x

/-- The centre-odd part of the change `s₀ ↦ s`. -/
def delta1 (c : S → S) (H : S → α → ℝ) (s₀ s : S) (x : α) : ℝ := (H s x - H s₀ x) - delta0 c H s₀ s x

theorem delta0_add_delta1 (c : S → S) (H : S → α → ℝ) (s₀ s : S) (x : α) :
    delta0 c H s₀ s x + delta1 c H s₀ s x = H s x - H s₀ x := by
  unfold delta1; ring

/-- A pure centre flip has no centre-blind part. -/
theorem delta0_centre_flip {c : S → S} (hc : ∀ s, c (c s) = s) (H : S → α → ℝ) (s₀ : S) (x : α) :
    delta0 c H s₀ (c s₀) x = 0 := by
  unfold delta0 centreBar; rw [hc]; ring

/-- The centre-blind part does not see the centre part of the new value. -/
theorem delta0_centre_blind {c : S → S} (hc : ∀ s, c (c s) = s) (H : S → α → ℝ) (s₀ s : S) (x : α) :
    delta0 c H s₀ (c s) x = delta0 c H s₀ s x := by
  unfold delta0 centreBar; rw [hc]; ring

/-- Centre-odd weights (`H (c s) = - H s`; the U(1) Wilson term under `θ ↦ θ + π`) have no centre-blind part. -/
theorem delta0_eq_zero_of_odd {c : S → S} {H : S → α → ℝ} (hodd : ∀ s x, H (c s) x = - H s x) (s₀ s : S)
    (x : α) : delta0 c H s₀ s x = 0 := by
  unfold delta0 centreBar; rw [hodd, hodd]; ring

/-- Centre-even weights have no centre-odd part. -/
theorem delta1_eq_zero_of_even {c : S → S} {H : S → α → ℝ} (heven : ∀ s x, H (c s) x = H s x) (s₀ s : S)
    (x : α) : delta1 c H s₀ s x = 0 := by
  unfold delta1 delta0 centreBar; rw [heven, heven]; ring

end CentreSplit

/-! ## 4. Mixtures over the same centre law -/

section Mixture

variable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]

theorem integral_bind_eq (μ : Measure Z) [IsProbabilityMeasure μ] (K : Kernel Z X) [IsMarkovKernel K]
    {F : X → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ x, |F x| ≤ M) :
    ∫ x, F x ∂(μ.bind K) = ∫ ζ, ∫ x, F x ∂(K ζ) ∂μ := by
  have hi : Integrable F ((K ∘ₖ Kernel.const Unit μ) ()) := integrable_of_abs_le hF hFM
  have h := Kernel.integral_comp hi
  rw [Kernel.comp_apply, Kernel.const_apply] at h
  exact h

theorem integrable_integral_kernel (μ : Measure Z) [IsProbabilityMeasure μ] (K : Kernel Z X) [IsMarkovKernel K]
    {F : X → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ x, |F x| ≤ M) :
    Integrable (fun ζ => ∫ x, F x ∂(K ζ)) μ := by
  have hi : Integrable F ((K ∘ₖ Kernel.const Unit μ) ()) := integrable_of_abs_le hF hFM
  have h := hi.integral_comp
  rw [Kernel.const_apply] at h
  exact h

theorem abs_integral_kernel_le (K : Kernel Z X) [IsMarkovKernel K] {F : X → ℝ} {M : ℝ}
    (hFM : ∀ x, |F x| ≤ M) (ζ : Z) : |∫ x, F x ∂(K ζ)| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := K ζ) (f := F) (C := M)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hFM x)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
  exact h

/-- **Mixtures over the same law** (S). If `q = μ.bind K` and `r = μ.bind K'` (the same centre law `μ`, different
adjoint kernels), and the per-component averages differ by at most `ε` on a measurable good set `G`, then
`|∫ F dq - ∫ F dr| ≤ ε + 2 M μ(Gᶜ)`. -/
theorem abs_integral_bind_sub_le (μ : Measure Z) [IsProbabilityMeasure μ] (K K' : Kernel Z X) [IsMarkovKernel K]
    [IsMarkovKernel K'] {F : X → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ x, |F x| ≤ M) {G : Set Z}
    (hG : MeasurableSet G) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ ζ ∈ G, |∫ x, F x ∂(K ζ) - ∫ x, F x ∂(K' ζ)| ≤ ε) :
    |∫ x, F x ∂(μ.bind K) - ∫ x, F x ∂(μ.bind K')| ≤ ε + 2 * M * μ.real Gᶜ := by
  obtain ⟨x₀⟩ : Nonempty X := by
    obtain ⟨ζ⟩ : Nonempty Z := by
      obtain ⟨ζ, -⟩ := nonempty_of_measure_ne_zero (μ := μ) (s := Set.univ) (by simp)
      exact ⟨ζ⟩
    obtain ⟨x, -⟩ := nonempty_of_measure_ne_zero (μ := K ζ) (s := Set.univ) (by simp)
    exact ⟨x⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans (hFM x₀)
  rw [integral_bind_eq μ K hF hFM, integral_bind_eq μ K' hF hFM]
  have i1 := integrable_integral_kernel μ K hF hFM
  have i2 := integrable_integral_kernel μ K' hF hFM
  rw [← integral_sub i1 i2]
  have ib : Integrable (fun ζ => ε + Gᶜ.indicator (fun _ => 2 * M) ζ) μ :=
    (integrable_const ε).add ((integrable_const (2 * M)).indicator hG.compl)
  calc |∫ ζ, (∫ x, F x ∂(K ζ) - ∫ x, F x ∂(K' ζ)) ∂μ|
      ≤ ∫ ζ, |∫ x, F x ∂(K ζ) - ∫ x, F x ∂(K' ζ)| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ)
          (fun ζ => ∫ x, F x ∂(K ζ) - ∫ x, F x ∂(K' ζ))
    _ ≤ ∫ ζ, (ε + Gᶜ.indicator (fun _ => 2 * M) ζ) ∂μ := by
        refine integral_mono (i1.sub i2).abs ib fun ζ => ?_
        show |∫ x, F x ∂(K ζ) - ∫ x, F x ∂(K' ζ)| ≤ ε + Gᶜ.indicator (fun _ => 2 * M) ζ
        by_cases hζ : ζ ∈ G
        · have : Gᶜ.indicator (fun _ => 2 * M) ζ = 0 :=
            Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hζ) _
          rw [this, add_zero]; exact hε ζ hζ
        · rw [Set.indicator_of_mem (Set.mem_compl hζ)]
          have h1 := abs_integral_kernel_le K hFM ζ
          have h2 := abs_integral_kernel_le K' hFM ζ
          have : |∫ x, F x ∂(K ζ) - ∫ x, F x ∂(K' ζ)| ≤ 2 * M := by
            rw [abs_le] at h1 h2 ⊢; constructor <;> linarith
          linarith
    _ = ε + 2 * M * μ.real Gᶜ := by
        rw [integral_add (integrable_const ε) ((integrable_const (2 * M)).indicator hG.compl),
          integral_const, integral_indicator_const _ hG.compl]
        simp [smul_eq_mul, probReal_univ]
        ring

end Mixture

end ProofPhase.Adjoint2
