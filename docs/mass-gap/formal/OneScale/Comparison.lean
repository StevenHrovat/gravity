/-
The one-scale reduction, abstract layer (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, Lemma 2.5 and Step 1 of the proof of Theorem A (§4.1).
-/

import OneScale.Blocks

/-!
# Propagation of oscillations and the contraction step

* `osc_blockAvg_of_not_mem`: **Lemma 2.5 (H)** for one block: for `x ∉ B`,
  `δ_x(P_B h) ≤ δ_x(h) + k_B(x) · max_{y ∈ B} δ_y(h)`; for `x ∈ B`, `δ_x(P_B h) = 0` (`blockAvg_update_mem`).
* `BlockSpec.avg`: the averaged operator `P = M⁻¹ ∑_j P_{B_j}` (`M` the number of blocks), with `μ(P h) = μ(h)`.
* `BlockSpec.oscBound_avg`: **Step 1 (contraction)**: if `δ_x(h) ≤ N w(x)` for a weight `w ≥ 0` with
  `w(y) ≤ E w(x)` whenever `k_j(x) ≠ 0` and `y ∈ B_j`, and GDS holds with `γ E ≤ 1`, then
  `δ_x(P h) ≤ (1 - c₋ (1 - γE)/M) N w(x)`.

This is the Dobrushin–Foellmer comparison step (Dobrushin 1970, Foellmer 1982) in the block form of
Dobrushin–Shlosman (1985); the formulation without a frozen set `S` follows the proof note (correction C1).
-/

open MeasureTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-- **Lemma 2.5 (H), one block, `x` outside the block.** If `k` is an influence bound for `x` on the block `B` and
`δ_y(h) ≤ m` on `B`, then `δ_x(P_B h) ≤ δ_x(h) + k m`. -/
theorem osc_blockAvg_of_not_mem {B : Finset ι} {q : (ι → S) → Measure (ι → S)}
    [∀ σ, IsProbabilityMeasure (q σ)] {x : ι} (hx : x ∉ B) {k : ℝ} (hk : IsInfluenceBound B q x k)
    {h : (ι → S) → ℝ} (hh : BM h) {v : ι → ℝ} (hv : OscBound h v) {m : ℝ} (hm : ∀ y ∈ B, v y ≤ m)
    (σ : ι → S) (s : S) :
    |blockAvg B q h σ - blockAvg B q h (Function.update σ x s)| ≤ v x + k * m := by
  set σ' := Function.update σ x s
  set F : (ι → S) → ℝ := fun ξ => h (splice B σ' ξ)
  obtain ⟨C, hC⟩ := hh.bdd
  have hF : BM F := ⟨hh.meas.comp (measurable_splice_right B σ'), ⟨C, fun ξ => hC _⟩⟩
  have hFdep : DepOn F B := by
    intro ξ ξ' he
    simp only [F]
    congr 1
    funext i
    by_cases hi : i ∈ B
    · simp [splice, hi, he i hi]
    · simp [splice, hi]
  have hFosc : ∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ m := by
    intro ξ y t hy
    simp only [F]
    rw [splice_update_right hy]
    exact (hv _ y t).trans (hm y hy)
  have h1 : |∫ ξ, (h (splice B σ ξ) - F ξ) ∂(q σ)| ≤ v x := by
    have := norm_integral_le_of_norm_le_const (μ := q σ) (f := fun ξ => h (splice B σ ξ) - F ξ) (C := v x)
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs]
        simp only [F, σ']
        rw [splice_update_left hx]
        exact hv _ x s)
    simpa [Real.norm_eq_abs] using this
  have h2 := hk σ s F m hF hFdep hFosc
  have hsplit : blockAvg B q h σ - blockAvg B q h σ' =
      ∫ ξ, (h (splice B σ ξ) - F ξ) ∂(q σ) + (∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q σ')) := by
    unfold blockAvg
    rw [integral_sub (integrable_comp_splice hh σ _) (hF.integrable _)]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

namespace BlockSpec

variable {J : Type*} [Fintype J] {μ : Measure (ι → S)} (P : BlockSpec μ J)

/-- The averaged operator `P h = M⁻¹ ∑_j P_{B_j} h`. -/
def avg (h : (ι → S) → ℝ) (σ : ι → S) : ℝ :=
  (Fintype.card J : ℝ)⁻¹ * ∑ j, blockAvg (P.block j) (P.spec j) h σ

theorem bm_avg' {h : (ι → S) → ℝ} (hh : BM h) : BM (P.avg h) :=
  (BM.sum univ (fun j => P.bm_avg j hh)).const_mul _

/-- `μ(P h) = μ(h)` (from the DLR identity of every block). -/
theorem integral_avg [IsFiniteMeasure μ] [Nonempty J] {h : (ι → S) → ℝ} (hh : BM h) :
    ∫ σ, P.avg h σ ∂μ = ∫ σ, h σ ∂μ := by
  unfold avg
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => (P.bm_avg j hh).integrable μ)]
  simp_rw [P.dlr _ _ hh]
  rw [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),
    one_mul]

/-- The number of blocks is at least the coverage of any index. -/
theorem coverage_le_card (x : ι) : coverage P.block x ≤ Fintype.card J := by
  unfold coverage
  exact (card_filter_le _ _).trans (by rw [card_univ])

/-- The number of blocks not containing `x` is `M - c(x)`. -/
theorem card_not_mem (x : ι) :
    (((univ : Finset J).filter fun j => x ∉ P.block j).card : ℝ) =
      (Fintype.card J : ℝ) - coverage P.block x := by
  have := card_filter_add_card_filter_not (s := (univ : Finset J)) (fun j => x ∈ P.block j)
  rw [card_univ] at this
  unfold coverage
  rw [← this]
  push_cast
  ring

/-- **Step 1 of Theorem A (contraction).** Under GDS, if `δ_x(h) ≤ N w(x)` for all `x`, where the weight `w ≥ 0`
grows by at most the factor `E` across every block boundary that carries influence, then
`δ_x(P h) ≤ (1 - c₋(1 - γE)/M) N w(x)`. -/
theorem oscBound_avg (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (k j z))
    {γ : ℝ} (hgds : GDS P.block k γ) {cmin : ℕ} (hcov : ∀ x, cmin ≤ coverage P.block x) (hc1 : 1 ≤ cmin)
    {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x) {E : ℝ} (hE : 0 ≤ E)
    (hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → k j x ≠ 0 → w y ≤ E * w x) (hρ : γ * E ≤ 1)
    {Nn : ℝ} (hN : 0 ≤ Nn) {h : (ι → S) → ℝ} (hh : BM h) (hv : OscBound h (fun x => Nn * w x)) :
    OscBound (P.avg h) (fun x => (1 - cmin * (1 - γ * E) / Fintype.card J) * (Nn * w x)) := by
  intro σ x s
  set σ' := Function.update σ x s
  set M : ℝ := (Fintype.card J : ℝ)
  have hM : (1 : ℝ) ≤ M := by
    have := (hc1.trans (hcov x)).trans (P.coverage_le_card x)
    simp only [M]
    exact_mod_cast this
  have hM0 : 0 < M := by linarith
  -- the per-block bound
  set t : J → ℝ := fun j =>
    |blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ'|
  have ht_in : ∀ j, x ∈ P.block j → t j = 0 := by
    intro j hj
    simp only [t, σ', blockAvg_update_mem (P.spec_congr j) h hj σ s, sub_self, abs_zero]
  have ht_out : ∀ j, x ∉ P.block j → t j ≤ Nn * w x + k j x * (Nn * (E * w x)) := by
    intro j hj
    by_cases hkz : k j x = 0
    · have hm : ∀ y ∈ P.block j, Nn * w y ≤ Nn * ∑ y' ∈ P.block j, w y' := fun y hy =>
        mul_le_mul_of_nonneg_left (single_le_sum (fun y' _ => hw0 y') hy) hN
      have := osc_blockAvg_of_not_mem hj (hk j x hj) hh hv hm σ s
      rw [hkz, zero_mul, add_zero] at this
      rw [hkz, zero_mul, add_zero]
      exact this
    · have hm : ∀ y ∈ P.block j, Nn * w y ≤ Nn * (E * w x) := fun y hy =>
        mul_le_mul_of_nonneg_left (hwk j x y hj hy hkz) hN
      exact osc_blockAvg_of_not_mem hj (hk j x hj) hh hv hm σ s
  have hsum : ∑ j, t j ≤ (M - coverage P.block x) * (Nn * w x) +
      Nn * E * w x * (γ * coverage P.block x) := by
    rw [← sum_filter_add_sum_filter_not univ (fun j => x ∈ P.block j)]
    rw [sum_eq_zero (fun j hj => ht_in j (mem_filter.1 hj).2), zero_add]
    calc ∑ j ∈ univ.filter (fun j => x ∉ P.block j), t j
        ≤ ∑ j ∈ univ.filter (fun j => x ∉ P.block j), (Nn * w x + k j x * (Nn * (E * w x))) :=
          sum_le_sum fun j hj => ht_out j (mem_filter.1 hj).2
      _ = (M - coverage P.block x) * (Nn * w x) +
          Nn * E * w x * ∑ j ∈ univ.filter (fun j => x ∉ P.block j), k j x := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, P.card_not_mem x, mul_sum]
          congr 1
          refine sum_congr rfl fun j _ => ?_
          ring
      _ ≤ _ := by
          gcongr
          · exact mul_nonneg (mul_nonneg hN hE) (hw0 x)
          · exact hgds x
  have hdiff : P.avg h σ - P.avg h σ' =
      M⁻¹ * ∑ j, (blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ') := by
    unfold avg; rw [sum_sub_distrib]; ring
  have hNw : 0 ≤ Nn * w x := mul_nonneg hN (hw0 x)
  have hcx : (cmin : ℝ) ≤ coverage P.block x := by exact_mod_cast hcov x
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 hM0)]
  calc M⁻¹ * |∑ j, (blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ')|
      ≤ M⁻¹ * ∑ j, t j := mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (inv_nonneg.2 hM0.le)
    _ ≤ M⁻¹ * ((M - coverage P.block x) * (Nn * w x) + Nn * E * w x * (γ * coverage P.block x)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hM0.le)
    _ = M⁻¹ * ((M - coverage P.block x * (1 - γ * E)) * (Nn * w x)) := by ring
    _ ≤ M⁻¹ * ((M - cmin * (1 - γ * E)) * (Nn * w x)) := by
        gcongr
    _ = (1 - cmin * (1 - γ * E) / M) * (Nn * w x) := by
        field_simp

end BlockSpec

end OneScale
