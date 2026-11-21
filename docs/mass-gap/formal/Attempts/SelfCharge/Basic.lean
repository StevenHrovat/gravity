/-
Attempt round 2026-11-21, route (d) "self-charge". Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/selfcharge/NOTE.md` (sections 2-5).
-/

import Mathlib

/-!
# Self-charge: three exact facts and one obstruction

* **Local flatness** (`norm_comm_le`, `norm_group_comm_le`): in any normed ring,
  `a k - k a = (a - 1)(k - 1) - (k - 1)(a - 1)`, so `‖a k - k a‖ ≤ 2 ‖a - 1‖ ‖k - 1‖`; for unitaries (inverses of norm
  `≤ 1`) the group commutator obeys `‖a k a⁻¹ k⁻¹ - 1‖ ≤ 2 ‖a - 1‖ ‖k - 1‖`. Every effect of non-commutativity is
  **quadratic** in the deviations from the identity: at weak coupling (links within `O(g)` of `1`) it is `O(g²)` per pair.
  Abelian case (`group_comm_of_comm`): the commutator is exactly `1` (photon, `Z₂`).
* **Diamagnetic deficit identity** (`deficit_identity`): for vectors `v_i` (the transports `ρ(U_ω)` of walks `ω`, in the
  Hilbert–Schmidt space) and weights `w_i`, `‖Σ w_i v_i‖² = c (Σ w_i)² - Σ_{i,j} w_i w_j (c - ⟪v_i, v_j⟫)`, and with
  `‖v_i‖² = c` the shortfall is `c - ⟪v_i, v_j⟫ = ½ ‖v_i - v_j‖² ≥ 0` (`shortfall_eq`). Hence the covariant response is
  never above the free one (`diamagnetic`), it equals the free one when all transports agree (`photon_no_deficit`: the
  trivial adjoint action of an abelian group), and it is strictly below by `δ (W² - Σ w_i²)` when every pair of distinct
  walks has shortfall `≥ δ` (`deficit_strict`).
* **Centre invisibility** (`su2_adj_shortfall`, `su2_adj_shortfall_zero_iff`): for `SU(2)`, `χ_adj = χ_f² - 1 = 4a₀² - 1`,
  so the adjoint shortfall `3 - χ_adj = 4(1 - a₀²)` vanishes exactly at the centre `a₀ = ±1` (the MG3 twists).
* **Sharp-coefficient lemma** (`layers_reach`, `scale_bounded`, `scale_unbounded`): a layer inequality
  `y_{j+1} ≤ y_j - c` for an inverse coupling `y` reaches a threshold `y*` within `⌈(y₀ - y*)/c⌉` layers; with the lattice
  spacing of the true flow, `a Λ = 2^{-y₀/c₀}`, the guaranteed block scale `log₂(L Λ) = J - y₀/c₀` stays bounded as
  `y₀ → ∞` when `c ≥ c₀`, and tends to `+∞` when `c < c₀`. A self-charge inequality that loses any constant in the
  per-layer price gives no uniform physical scale.

Nothing here proves `UniformGDS`; these are the exact pieces route (d) found, and the obstruction it ran into.
-/

open Finset Filter Topology

noncomputable section

namespace Attempts.SelfCharge

/-! ## 1. Local flatness -/

/-- The commutator of `a` and `k` written through their deviations from the identity. -/
theorem comm_eq {R : Type*} [Ring R] (a k : R) :
    a * k - k * a = (a - 1) * (k - 1) - (k - 1) * (a - 1) := by
  noncomm_ring

/-- **Local flatness:** `‖a k - k a‖ ≤ 2 ‖a - 1‖ ‖k - 1‖` in any normed ring. -/
theorem norm_comm_le {R : Type*} [NormedRing R] (a k : R) :
    ‖a * k - k * a‖ ≤ 2 * ‖a - 1‖ * ‖k - 1‖ := by
  rw [comm_eq]
  calc ‖(a - 1) * (k - 1) - (k - 1) * (a - 1)‖
      ≤ ‖(a - 1) * (k - 1)‖ + ‖(k - 1) * (a - 1)‖ := norm_sub_le _ _
    _ ≤ ‖a - 1‖ * ‖k - 1‖ + ‖k - 1‖ * ‖a - 1‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖a - 1‖ * ‖k - 1‖ := by ring

/-- The group commutator minus one, through the ring commutator (`ai`, `ki` right inverses of `a`, `k`). -/
theorem group_comm_eq {R : Type*} [Ring R] (a k ai ki : R) (ha : a * ai = 1) (hk : k * ki = 1) :
    a * k * ai * ki - 1 = (a * k - k * a) * (ai * ki) := by
  have h1 : k * a * (ai * ki) = 1 := by
    rw [show k * a * (ai * ki) = k * (a * ai) * ki by noncomm_ring, ha, mul_one, hk]
  rw [sub_mul, h1]
  noncomm_ring

/-- **Local flatness, group form:** for unitaries (inverses of norm `≤ 1`),
`‖a k a⁻¹ k⁻¹ - 1‖ ≤ 2 ‖a - 1‖ ‖k - 1‖`. -/
theorem norm_group_comm_le {R : Type*} [NormedRing R] (a k ai ki : R) (ha : a * ai = 1) (hk : k * ki = 1)
    (hai : ‖ai‖ ≤ 1) (hki : ‖ki‖ ≤ 1) :
    ‖a * k * ai * ki - 1‖ ≤ 2 * ‖a - 1‖ * ‖k - 1‖ := by
  rw [group_comm_eq a k ai ki ha hk]
  have hp : ‖ai * ki‖ ≤ 1 :=
    (norm_mul_le _ _).trans (by nlinarith [norm_nonneg ai, norm_nonneg ki])
  calc ‖(a * k - k * a) * (ai * ki)‖ ≤ ‖a * k - k * a‖ * ‖ai * ki‖ := norm_mul_le _ _
    _ ≤ ‖a * k - k * a‖ * 1 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ ≤ 2 * ‖a - 1‖ * ‖k - 1‖ := by rw [mul_one]; exact norm_comm_le a k

/-- **Abelian case (photon, `Z₂`):** commuting transports have trivial group commutator. -/
theorem group_comm_of_comm {R : Type*} [Ring R] (a k ai ki : R) (ha : a * ai = 1) (hk : k * ki = 1)
    (hc : a * k = k * a) : a * k * ai * ki = 1 := by
  have h := group_comm_eq a k ai ki ha hk
  have h2 : a * k - k * a = 0 := sub_eq_zero.2 hc
  rw [h2, zero_mul] at h
  exact sub_eq_zero.1 h

/-! ## 2. The diamagnetic deficit identity -/

section Deficit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}

/-- The squared norm of a weighted sum, expanded over pairs. -/
theorem norm_sq_sum (s : Finset ι) (w : ι → ℝ) (v : ι → E) :
    ‖∑ i ∈ s, w i • v i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, w i * w j * @inner ℝ E _ (v i) (v j) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- **Deficit identity:** for any constant `c`,
`‖Σ w_i v_i‖² = c (Σ w_i)² - Σ_{i,j} w_i w_j (c - ⟪v_i, v_j⟫)`. With `v_i = ρ(U_{ω_i})` and `c = dim ρ`, the term
`c - ⟪v_i, v_j⟫ = dim ρ - Re χ_ρ(U_{ω_i} U_{ω_j}⁻¹)` is the shortfall of the loop `ω_i ω_j⁻¹`. -/
theorem deficit_identity (s : Finset ι) (w : ι → ℝ) (v : ι → E) (c : ℝ) :
    ‖∑ i ∈ s, w i • v i‖ ^ 2 =
      c * (∑ i ∈ s, w i) ^ 2 - ∑ i ∈ s, ∑ j ∈ s, w i * w j * (c - @inner ℝ E _ (v i) (v j)) := by
  rw [norm_sq_sum, sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The shortfall is half a squared distance:** if `‖x‖² = ‖y‖² = c`, then `c - ⟪x, y⟫ = ½ ‖x - y‖² ≥ 0`. -/
theorem shortfall_eq (x y : E) (c : ℝ) (hx : ‖x‖ ^ 2 = c) (hy : ‖y‖ ^ 2 = c) :
    c - @inner ℝ E _ (x) (y) = ‖x - y‖ ^ 2 / 2 := by
  rw [norm_sub_sq_real, hx, hy]; ring

theorem shortfall_nonneg (x y : E) (c : ℝ) (hx : ‖x‖ ^ 2 = c) (hy : ‖y‖ ^ 2 = c) :
    0 ≤ c - @inner ℝ E _ (x) (y) := by
  rw [shortfall_eq x y c hx hy]; positivity

/-- **Diamagnetic inequality:** with nonnegative weights and transports of equal norm, the covariant sum is never above
the free one: `‖Σ w_i v_i‖² ≤ c (Σ w_i)²`. -/
theorem diamagnetic (s : Finset ι) (w : ι → ℝ) (v : ι → E) (c : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hv : ∀ i ∈ s, ‖v i‖ ^ 2 = c) :
    ‖∑ i ∈ s, w i • v i‖ ^ 2 ≤ c * (∑ i ∈ s, w i) ^ 2 := by
  rw [deficit_identity s w v c]
  have : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * (c - @inner ℝ E _ (v i) (v j)) :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (shortfall_nonneg _ _ c (hv i hi) (hv j hj))
  exact sub_le_self _ this

/-- **Photon case:** if all transports agree (the adjoint action of an abelian group is trivial, so the photon's own
disturbance is transported by the identity along every walk), there is no deficit: the response is the free one. -/
theorem photon_no_deficit (s : Finset ι) (w : ι → ℝ) (u : E) (c : ℝ) (hu : ‖u‖ ^ 2 = c) :
    ‖∑ i ∈ s, w i • u‖ ^ 2 = c * (∑ i ∈ s, w i) ^ 2 := by
  rw [deficit_identity s w (fun _ => u) c]
  simp only [real_inner_self_eq_norm_sq, hu, sub_self, mul_zero, Finset.sum_const_zero, sub_zero]

/-- **Strict deficit:** if every pair of distinct walks has loop shortfall at least `δ ≥ 0`, the covariant response is
below the free one by at least `δ (W² - Σ w_i²)`, `W = Σ w_i`. -/
theorem deficit_strict (s : Finset ι) (w : ι → ℝ) (v : ι → E) (c δ : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hv : ∀ i ∈ s, ‖v i‖ ^ 2 = c) (hδ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ c - @inner ℝ E _ (v i) (v j)) :
    ‖∑ i ∈ s, w i • v i‖ ^ 2 ≤
      c * (∑ i ∈ s, w i) ^ 2 - δ * ((∑ i ∈ s, w i) ^ 2 - ∑ i ∈ s, w i ^ 2) := by
  classical
  rw [deficit_identity s w v c]
  -- pointwise: w_i w_j sf_ij ≥ w_i w_j δ - [i = j] w_i w_j δ
  have hpt : ∀ i ∈ s, ∀ j ∈ s,
      w i * w j * δ - (if i = j then w i * w j * δ else 0) ≤ w i * w j * (c - @inner ℝ E _ (v i) (v j)) := by
    intro i hi j hj
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, sub_self, real_inner_self_eq_norm_sq, hv i hi, sub_self, mul_zero]
    · rw [if_neg hij, sub_zero]
      exact mul_le_mul_of_nonneg_left (hδ i hi j hj hij) (mul_nonneg (hw i hi) (hw j hj))
  have hsum : ∑ i ∈ s, ∑ j ∈ s, (w i * w j * δ - (if i = j then w i * w j * δ else 0)) ≤
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (c - @inner ℝ E _ (v i) (v j)) :=
    Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpt i hi j hj
  have hleft : ∑ i ∈ s, ∑ j ∈ s, (w i * w j * δ - (if i = j then w i * w j * δ else 0)) =
      δ * ((∑ i ∈ s, w i) ^ 2 - ∑ i ∈ s, w i ^ 2) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq]
    rw [sq, Finset.sum_mul_sum, mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [if_pos hi]; ring
  linarith

end Deficit

/-! ## 3. Centre invisibility (SU(2), real algebra) -/

/-- For a unit quaternion `a₀ + a⃗` (`a₀² + r² = 1`, `r² = |a⃗|²`), the adjoint character is `3a₀² - r² = 4a₀² - 1`
(`= χ_f² - 1`, `χ_f = 2a₀`), and the adjoint shortfall is `3 - χ_adj = 4(1 - a₀²) ≥ 0`. -/
theorem su2_adj_shortfall (a₀ r2 : ℝ) (h : a₀ ^ 2 + r2 = 1) (hr : 0 ≤ r2) :
    3 * a₀ ^ 2 - r2 = 4 * a₀ ^ 2 - 1 ∧ 3 - (3 * a₀ ^ 2 - r2) = 4 * (1 - a₀ ^ 2) ∧
      0 ≤ 3 - (3 * a₀ ^ 2 - r2) := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The adjoint shortfall vanishes exactly at the centre `a₀ = ±1` (the MG3 twists are invisible to the adjoint). -/
theorem su2_adj_shortfall_zero_iff (a₀ : ℝ) : 4 * (1 - a₀ ^ 2) = 0 ↔ a₀ = 1 ∨ a₀ = -1 := by
  constructor
  · intro h
    have : (a₀ - 1) * (a₀ + 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-! ## 4. The sharp-coefficient lemma -/

/-- A layer inequality `y_{j+1} ≤ y_j - c` gives `y_J ≤ y_0 - J c`. -/
theorem layers_decrease (y : ℕ → ℝ) (c : ℝ) (h : ∀ j, y (j + 1) ≤ y j - c) (J : ℕ) :
    y J ≤ y 0 - J * c := by
  induction J with
  | zero => simp
  | succ J ih =>
    have := h J
    push_cast
    linarith

/-- The threshold `y*` is reached within any `J ≥ (y₀ - y*)/c` layers. -/
theorem layers_reach (y : ℕ → ℝ) (c ystar : ℝ) (hc : 0 < c) (h : ∀ j, y (j + 1) ≤ y j - c) (J : ℕ)
    (hJ : (y 0 - ystar) / c ≤ J) : y J ≤ ystar := by
  have h1 := layers_decrease y c h J
  have h2 : y 0 - ystar ≤ J * c := by rwa [div_le_iff₀ hc] at hJ
  linarith

/-- The number of layers the inequality guarantees, from inverse coupling `y₀` down to `y*`. -/
def layersNeeded (c ystar y₀ : ℝ) : ℕ := ⌈(y₀ - ystar) / c⌉₊

/-- `log₂(L Λ)` of the block scale reached after the guaranteed layers, when the lattice spacing follows the true flow
`a Λ = 2^{-y₀/c₀}`. -/
def logScale (c c₀ ystar y₀ : ℝ) : ℝ := (layersNeeded c ystar y₀ : ℝ) - y₀ / c₀

/-- **Sharp coefficient, sufficient side:** if the proved per-layer price `c` is at least the true one `c₀`, the
guaranteed block scale stays bounded in physical units: `log₂(L Λ) ≤ 1 - y*/c` for all `0 ≤ y* ≤ y₀`. -/
theorem scale_bounded {c c₀ ystar : ℝ} (hc0 : 0 < c₀) (hc : c₀ ≤ c) (y₀ : ℝ) (hy : ystar ≤ y₀) (hy0 : 0 ≤ y₀) :
    logScale c c₀ ystar y₀ ≤ 1 - ystar / c := by
  have hcpos : 0 < c := lt_of_lt_of_le hc0 hc
  unfold logScale layersNeeded
  have hx : 0 ≤ (y₀ - ystar) / c := div_nonneg (by linarith) hcpos.le
  have hceil := Nat.ceil_lt_add_one hx
  have hinv : y₀ / c ≤ y₀ / c₀ := div_le_div_of_nonneg_left hy0 hc0 hc
  have : (y₀ - ystar) / c = y₀ / c - ystar / c := by ring
  linarith

/-- **Sharp coefficient, necessary side:** if the proved price `c` is below the true one `c₀`, the guaranteed block
scale grows without bound in physical units as `y₀ → ∞` (the continuum limit): no uniform `L₀`. -/
theorem scale_unbounded {c c₀ ystar : ℝ} (hc : 0 < c) (hlt : c < c₀) :
    Tendsto (logScale c c₀ ystar) atTop atTop := by
  have hc0 : 0 < c₀ := hc.trans hlt
  have hk : 0 < 1 / c - 1 / c₀ := by
    rw [sub_pos]; exact one_div_lt_one_div_of_lt hc hlt
  have hlin : Tendsto (fun y : ℝ => (1 / c - 1 / c₀) * y + (-(ystar / c))) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop hk tendsto_id)
  refine tendsto_atTop_mono (fun y => ?_) hlin
  unfold logScale layersNeeded
  have := Nat.le_ceil ((y - ystar) / c)
  have e : (1 / c - 1 / c₀) * y + -(ystar / c) = (y - ystar) / c - y / c₀ := by
    field_simp
    ring
  rw [e]
  linarith

end Attempts.SelfCharge
