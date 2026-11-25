/-
Proof phase, M1 tools (m1-tools): local finite-rank modifications of a propagator (2026-11-22). Released under
Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/V1-INPUTS.md` (Lemma FR).
-/

import Mathlib

/-!
# Local modifications of a propagator: the algebra and the decay

The two inputs of `V1-EXCISION.md` (gauge fixing with the hole's boundary sites fixed, and the propagator bounds for the
locally modified constraint) both concern an operator `K` with a known inverse `G` (Balaban's bounds) and a modified
operator `K + V` (or a compression of `K`) that differs from it only on a finite set `S` near the hole. Lemma FR of
`V1-INPUTS.md` bounds the modified inverse by the old one. Its two elementary steps are machine-checked here:

* `resolvent_two_sided`: if `G K = 1 = K G` and `G̃ (K + V) = 1 = (K + V) G̃`, then
  `G̃ = G - G V G + G V G̃ V G` (in any ring; for operators supported on `S` the last two terms factor through `S`);
* `decay_through`: a kernel that factors through a set `S` of diameter `≤ D`, with both factors decaying like
  `exp(-δ dist)`, decays like `exp(-δ dist)` with the constant multiplied by `|S|² exp(δ D)`.

**Claim level.** Both proved (standard axioms). The operator-norm version of Lemma FR (weighted sup norms, as in
Balaban's Theorems 3.12 and 3.13 of `[5]`) and the positivity of the modified operator are on paper (`V1-INPUTS.md`).
-/

namespace ProofPhase.M1

/-- One side of the resolvent identity. -/
theorem resolvent_left {R : Type*} [Ring R] {K V G Gt : R} (hG : G * K = 1) (hGt : (K + V) * Gt = 1) :
    Gt = G - G * V * Gt :=
  calc Gt = (G * K) * Gt := by rw [hG, one_mul]
    _ = G * ((K + V) * Gt) - G * V * Gt := by noncomm_ring
    _ = G - G * V * Gt := by rw [hGt, mul_one]

/-- The other side. -/
theorem resolvent_right {R : Type*} [Ring R] {K V G Gt : R} (hG : K * G = 1) (hGt : Gt * (K + V) = 1) :
    Gt = G - Gt * V * G :=
  calc Gt = Gt * (K * G) := by rw [hG, mul_one]
    _ = (Gt * (K + V)) * G - Gt * V * G := by noncomm_ring
    _ = G - Gt * V * G := by rw [hGt, one_mul]

/-- **The two-sided resolvent identity:** `G̃ = G - G V G + G V G̃ V G`. If `V` is supported on a finite set `S`
(`V = P_S V P_S`), the correction terms factor through `S`, which is what Lemma FR uses. -/
theorem resolvent_two_sided {R : Type*} [Ring R] {K V G Gt : R} (hGl : G * K = 1) (hGr : K * G = 1)
    (hGtl : Gt * (K + V) = 1) (hGtr : (K + V) * Gt = 1) :
    Gt = G - G * V * G + G * V * Gt * V * G := by
  have h1 := resolvent_left hGl hGtr
  have h2 := resolvent_right hGr hGtl
  calc Gt = G - G * V * Gt := h1
    _ = G - G * V * (G - Gt * V * G) := by rw [← h2]
    _ = G - G * V * G + G * V * Gt * V * G := by noncomm_ring

/-- **Decay through a finite set.** If `|a x z| ≤ C₁ exp(-δ dist x z)`, `|b z' y| ≤ C₂ exp(-δ dist z' y)`,
`|M z z'| ≤ C₃` on a finite set `S` of diameter `≤ D`, then the kernel `Σ_{z, z' ∈ S} a x z M z z' b z' y` decays like
`exp(-δ dist x y)`, with constant `|S|² C₁ C₂ C₃ exp(δ D)`. -/
theorem decay_through {X : Type*} [PseudoMetricSpace X] (S : Finset X) {D δ C₁ C₂ C₃ : ℝ} (hδ : 0 ≤ δ)
    (hD : ∀ z ∈ S, ∀ z' ∈ S, dist z z' ≤ D) (a M b : X → X → ℝ) (x y : X)
    (ha : ∀ z ∈ S, |a x z| ≤ C₁ * Real.exp (-δ * dist x z))
    (hb : ∀ z' ∈ S, |b z' y| ≤ C₂ * Real.exp (-δ * dist z' y))
    (hM : ∀ z ∈ S, ∀ z' ∈ S, |M z z'| ≤ C₃) (hC₃ : 0 ≤ C₃) :
    |∑ z ∈ S, ∑ z' ∈ S, a x z * M z z' * b z' y| ≤
      (S.card : ℝ) ^ 2 * (C₁ * C₂ * C₃ * Real.exp (δ * D)) * Real.exp (-δ * dist x y) := by
  have hterm : ∀ z ∈ S, ∀ z' ∈ S,
      |a x z * M z z' * b z' y| ≤ C₁ * C₂ * C₃ * Real.exp (δ * D) * Real.exp (-δ * dist x y) := by
    intro z hz z' hz'
    have hC₁ : 0 ≤ C₁ := by
      have := ha z hz
      have he := Real.exp_pos (-δ * dist x z)
      nlinarith [abs_nonneg (a x z)]
    have hC₂ : 0 ≤ C₂ := by
      have := hb z' hz'
      have he := Real.exp_pos (-δ * dist z' y)
      nlinarith [abs_nonneg (b z' y)]
    have htri : dist x y ≤ dist x z + D + dist z' y := by
      have := dist_triangle4 x z z' y
      linarith [hD z hz z' hz']
    have hexp : Real.exp (-δ * dist x z) * Real.exp (-δ * dist z' y) ≤
        Real.exp (δ * D) * Real.exp (-δ * dist x y) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [abs_mul, abs_mul]
    calc |a x z| * |M z z'| * |b z' y|
        ≤ (C₁ * Real.exp (-δ * dist x z)) * C₃ * (C₂ * Real.exp (-δ * dist z' y)) := by
          gcongr
          · exact ha z hz
          · exact hM z hz z' hz'
          · exact hb z' hz'
      _ = C₁ * C₂ * C₃ * (Real.exp (-δ * dist x z) * Real.exp (-δ * dist z' y)) := by ring
      _ ≤ C₁ * C₂ * C₃ * (Real.exp (δ * D) * Real.exp (-δ * dist x y)) := by
          gcongr
      _ = C₁ * C₂ * C₃ * Real.exp (δ * D) * Real.exp (-δ * dist x y) := by ring
  calc |∑ z ∈ S, ∑ z' ∈ S, a x z * M z z' * b z' y|
      ≤ ∑ z ∈ S, ∑ z' ∈ S, |a x z * M z z' * b z' y| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum fun z _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ S, ∑ z' ∈ S, C₁ * C₂ * C₃ * Real.exp (δ * D) * Real.exp (-δ * dist x y) :=
        Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun z' hz' => hterm z hz z' hz'
    _ = (S.card : ℝ) ^ 2 * (C₁ * C₂ * C₃ * Real.exp (δ * D)) * Real.exp (-δ * dist x y) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

end ProofPhase.M1
