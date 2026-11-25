/-
The one-scale reduction, effective-theory layer: (H2) as positive coarse Ricci curvature (2026-11-21).
Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/H2-CURVATURE.md`, sections 2 and 3.
-/

import OneScale.Lipschitz

/-!
# Coarse Ricci curvature of the random-block heat bath, and the W-form block Dobrushin condition

Setting as in `OneScale.Blocks`: configurations `ι → S` on a finite index set, a cost `c : S → S → ℝ` with `c ≥ 0` and
`c a a = 0`, weights `w ≥ 0`, and the **weighted `ℓ¹` cost distance** `d_w(σ, σ') = ∑_x w_x c(σ_x, σ'_x)` (for `w ≡ 1`
the Hamming-type `ℓ¹` distance built from the link cost; if `c` is a metric, so is `d_w` for `w > 0`).

The kernel is the **random-block heat bath** `K = P.avg = M⁻¹ ∑_j P_{B_j}`: pick one of the `M` blocks uniformly and
resample it from its specification. Ollivier (J. Funct. Anal. 256 (2009), Def. 3 and Prop. 28 in the arXiv v4
numbering) defines `κ(σ, σ') = 1 - W₁(K_σ, K_σ') / d(σ, σ')` and shows that `κ(σ, σ') ≥ κ` for all pairs is
equivalent to the **Lipschitz contraction** `‖K h‖_Lip ≤ (1 - κ) ‖h‖_Lip`. We take the Lipschitz form as the definition
(`CoarseRicciLB`); its equality with the transport form is Kantorovich–Rubinstein duality (literature, not proved here).

* `isLipW_of_lipBound`, `lipBound_of_isLipW`: a function is `L`-Lipschitz for `d_w` iff `L_x(h) ≤ L w_x` for every
  single coordinate (local-to-global along single-coordinate paths; Ollivier's Prop. 19 in this product setting).
* `IsInfluenceBoundWAt`: the **pointwise** W influence of `z` on a block at one boundary condition `σ` and one new value
  `s` (the dual Wasserstein distance of the two block laws, divided by `c(σ_z, s)`).
* `BlockSpec.lipBound_avg_at`: the contraction step of Theorem A (W) under the **pointwise** GDS
  `∑_{j ∌ z} k_j(z; σ, s) ≤ γ c(z)` for every `σ, s` (the supremum outside the sum, weaker than `GDS`).
* **`BlockSpec.coarseRicci_of_gdsAt`**, **`BlockSpec.coarseRicci_of_gds`**: pointwise W-GDS (resp. W-GDS) with
  `γ E ≤ 1` gives coarse Ricci curvature `κ ≥ c₋ (1 - γ E) / M` of `K` for `d_w`; `coarseRicci_of_gds_flat` is the
  unweighted case `κ ≥ c₋ (1 - γ) / M`.
* `CoarseRicciLB.iterate`: `‖K^t h‖_Lip ≤ (1 - κ)^t ‖h‖_Lip`.
* **`BlockSpec.coarseRicci_le_coverage`**: conversely, any curvature bound satisfies
  `(1 - c(x)/M) |φ(a) - φ(s)| ≤ (1 - κ) c(a, s)` for every 1-Lipschitz bounded measurable `φ : S → ℝ`; with
  `φ = c(·, s)` (when `c` is a metric) this is `κ ≤ c(x)/M`, so the normalisation `c₋/M` is sharp.

Theorem A's covariance bound (`BlockSpec.theoremA_W`) uses only the contraction step, so its proof is exactly
"positive coarse Ricci curvature in the exponentially weighted metrics `d_w`, `w = e^{λ dist(·, S_g)}`" plus the block
covariance identity.
-/

open MeasureTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale

variable {ι S : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The weighted `ℓ¹` cost distance and Lipschitz functions -/

/-- The weighted `ℓ¹` cost distance `d_w(σ, σ') = ∑_x w_x c(σ_x, σ'_x)`. -/
def wdist (c : S → S → ℝ) (w : ι → ℝ) (σ σ' : ι → S) : ℝ := ∑ x, w x * c (σ x) (σ' x)

/-- `h` is `L`-Lipschitz for `d_w`. -/
def IsLipW (c : S → S → ℝ) (w : ι → ℝ) (h : (ι → S) → ℝ) (L : ℝ) : Prop :=
  ∀ σ σ' : ι → S, |h σ - h σ'| ≤ L * wdist c w σ σ'

theorem wdist_update (c : S → S → ℝ) (hc : ∀ a, c a a = 0) (w : ι → ℝ) (σ : ι → S) (x : ι) (s : S) :
    wdist c w σ (Function.update σ x s) = w x * c (σ x) s := by
  unfold wdist
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [Function.update_of_ne hy, hc])
    (fun h => absurd (Finset.mem_univ x) h)]
  simp

/-- **Local to global.** Single-coordinate Lipschitz bounds `L_x(h) ≤ L w_x` give `L`-Lipschitz for `d_w`. -/
theorem isLipW_of_lipBound {c : S → S → ℝ} {w : ι → ℝ} {h : (ι → S) → ℝ} {L : ℝ}
    (hv : LipBound c h (fun x => L * w x)) : IsLipW c w h L := by
  have key : ∀ T : Finset ι, ∀ {σ σ' : ι → S}, (∀ i ∉ T, σ i = σ' i) →
      |h σ - h σ'| ≤ ∑ x ∈ T, L * w x * c (σ x) (σ' x) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro σ σ' hT
      have : σ = σ' := funext fun i => hT i (Finset.notMem_empty i)
      simp [this]
    | insert a T ha ih =>
      intro σ σ' hT
      set σ'' := Function.update σ a (σ' a)
      have h1 : ∀ i ∉ T, σ'' i = σ' i := by
        intro i hi
        by_cases hia : i = a
        · subst hia; simp [σ'']
        · simp only [σ'', Function.update_of_ne hia]
          exact hT i (by simp [hia, hi])
      have h2 : ∑ x ∈ T, L * w x * c (σ'' x) (σ' x) = ∑ x ∈ T, L * w x * c (σ x) (σ' x) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxa : x ≠ a := fun h => ha (h ▸ hx)
        simp only [σ'', Function.update_of_ne hxa]
      rw [Finset.sum_insert ha]
      calc |h σ - h σ'| ≤ |h σ - h σ''| + |h σ'' - h σ'| := _root_.abs_sub_le _ _ _
        _ ≤ L * w a * c (σ a) (σ' a) + ∑ x ∈ T, L * w x * c (σ x) (σ' x) :=
          add_le_add (hv σ a (σ' a)) (h2 ▸ ih h1)
  intro σ σ'
  have := key Finset.univ (σ := σ) (σ' := σ') (fun i hi => absurd (Finset.mem_univ i) hi)
  refine this.trans (le_of_eq ?_)
  unfold wdist
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- **Global to local.** If `c a a = 0`, an `L`-Lipschitz function for `d_w` has `L_x(h) ≤ L w_x`. -/
theorem lipBound_of_isLipW {c : S → S → ℝ} (hc : ∀ a, c a a = 0) {w : ι → ℝ} {h : (ι → S) → ℝ} {L : ℝ}
    (hL : IsLipW c w h L) : LipBound c h (fun x => L * w x) := by
  intro σ x s
  have h1 := hL σ (Function.update σ x s)
  rw [wdist_update c hc] at h1
  show |h σ - h (Function.update σ x s)| ≤ L * w x * c (σ x) s
  rw [mul_assoc]
  exact h1

variable [MeasurableSpace S]

/-! ## Coarse Ricci curvature, Lipschitz (dual) form -/

/-- **Coarse Ricci curvature `≥ κ`** of a Markov operator `K` (acting on bounded measurable functions) for `d_w`, in
Ollivier's Lipschitz-contraction form: `K` maps `L`-Lipschitz functions to `(1 - κ) L`-Lipschitz functions. -/
def CoarseRicciLB (c : S → S → ℝ) (w : ι → ℝ) (K : ((ι → S) → ℝ) → ((ι → S) → ℝ)) (κ : ℝ) : Prop :=
  ∀ (h : (ι → S) → ℝ) (L : ℝ), BM h → 0 ≤ L → IsLipW c w h L → IsLipW c w (K h) ((1 - κ) * L)

/-- **Iteration.** `‖K^t h‖_Lip ≤ (1 - κ)^t ‖h‖_Lip`. -/
theorem CoarseRicciLB.iterate {c : S → S → ℝ} {w : ι → ℝ} {K : ((ι → S) → ℝ) → ((ι → S) → ℝ)} {κ : ℝ}
    (hK : CoarseRicciLB c w K κ) (hBM : ∀ h, BM h → BM (K h)) (hκ : κ ≤ 1) {h : (ι → S) → ℝ} (hh : BM h)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : IsLipW c w h L) (t : ℕ) :
    BM (K^[t] h) ∧ IsLipW c w (K^[t] h) ((1 - κ) ^ t * L) := by
  induction t with
  | zero => simpa using ⟨hh, hL⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨hBM _ ih.1, ?_⟩
    have hnn : 0 ≤ (1 - κ) ^ t * L := mul_nonneg (pow_nonneg (by linarith) t) hL0
    have := hK _ _ ih.1 hnn ih.2
    have e : (1 - κ) ^ (t + 1) * L = (1 - κ) * ((1 - κ) ^ t * L) := by ring
    rw [e]
    exact this

/-! ## Pointwise W influence and the pointwise contraction step -/

/-- **Pointwise W influence** of the outside coordinate `z` on the block specification `q`, at the boundary condition
`σ` and the new value `s`: for every bounded measurable `F` of the block with `L_y(F) ≤ L` on the block,
`|q^σ(F) - q^{σ^z}(F)| ≤ k L c(σ_z, s)`. `IsInfluenceBoundW` is this bound uniformly in `σ, s`. -/
def IsInfluenceBoundWAt (c : S → S → ℝ) (B : Finset ι) (q : (ι → S) → Measure (ι → S)) (z : ι) (σ : ι → S)
    (s : S) (k : ℝ) : Prop :=
  ∀ (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B →
    (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L * c (ξ y) t) →
    |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q (Function.update σ z s))| ≤ k * L * c (σ z) s

theorem IsInfluenceBoundW.at {c : S → S → ℝ} {B : Finset ι} {q : (ι → S) → Measure (ι → S)} {z : ι} {k : ℝ}
    (hk : IsInfluenceBoundW c B q z k) (σ : ι → S) (s : S) : IsInfluenceBoundWAt c B q z σ s k :=
  fun F L hF hFB hL => hk σ s F L hF hFB hL

/-- **Lemma 2.5 (W), pointwise.** As `lip_blockAvg_of_not_mem`, with the influence bound only at `(σ, s)`. -/
theorem lip_blockAvg_of_not_mem_at {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {B : Finset ι}
    {q : (ι → S) → Measure (ι → S)} [∀ σ, IsProbabilityMeasure (q σ)] {x : ι} (hx : x ∉ B) {σ : ι → S} {s : S}
    {k : ℝ} (hk : IsInfluenceBoundWAt c B q x σ s k) {h : (ι → S) → ℝ} (hh : BM h) {v : ι → ℝ}
    (hv : LipBound c h v) {m : ℝ} (hm : ∀ y ∈ B, v y ≤ m) :
    |blockAvg B q h σ - blockAvg B q h (Function.update σ x s)| ≤ (v x + k * m) * c (σ x) s := by
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
  have hFosc : ∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ m * c (ξ y) t := by
    intro ξ y t hy
    simp only [F]
    rw [splice_update_right hy]
    have := hv (splice B σ' ξ) y t
    rw [splice_of_mem hy] at this
    exact this.trans (mul_le_mul_of_nonneg_right (hm y hy) (hc0 _ _))
  have h1 : |∫ ξ, (h (splice B σ ξ) - F ξ) ∂(q σ)| ≤ v x * c (σ x) s := by
    have := norm_integral_le_of_norm_le_const (μ := q σ) (f := fun ξ => h (splice B σ ξ) - F ξ)
      (C := v x * c (σ x) s) (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs]
        simp only [F, σ']
        rw [splice_update_left hx]
        have := hv (splice B σ ξ) x s
        rwa [splice_of_not_mem hx] at this)
    simpa [Real.norm_eq_abs] using this
  have h2 := hk F m hF hFdep hFosc
  have hsplit : blockAvg B q h σ - blockAvg B q h σ' =
      ∫ ξ, (h (splice B σ ξ) - F ξ) ∂(q σ) + (∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q σ')) := by
    unfold blockAvg
    rw [integral_sub (integrable_comp_splice hh σ _) (hF.integrable _)]
    ring
  rw [hsplit]
  calc _ ≤ v x * c (σ x) s + k * m * c (σ x) s := (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = (v x + k * m) * c (σ x) s := by ring

namespace BlockSpec

variable {J : Type*} [Fintype J] {μ : Measure (ι → S)} (P : BlockSpec μ J)

/-- **The contraction step of Theorem A (W) under the pointwise GDS.** As `lipBound_avg`, with influence coefficients
`k j z σ s` that may depend on the boundary condition and the new value, and the GDS sum bounded at each `(σ, s)`. -/
theorem lipBound_avg_at {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) (k : J → ι → (ι → S) → S → ℝ)
    (hk : ∀ j z σ s, z ∉ P.block j → IsInfluenceBoundWAt c (P.block j) (P.spec j) z σ s (k j z σ s))
    {γ : ℝ} (hgds : ∀ z σ s, ∑ j ∈ univ.filter (fun j => z ∉ P.block j), k j z σ s ≤ γ * coverage P.block z)
    {cmin : ℕ} (hcov : ∀ x, cmin ≤ coverage P.block x) (hc1 : 1 ≤ cmin)
    {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x) {E : ℝ} (hE : 0 ≤ E)
    (hwk : ∀ j x y σ s, x ∉ P.block j → y ∈ P.block j → k j x σ s ≠ 0 → w y ≤ E * w x) (hρ : γ * E ≤ 1)
    {Nn : ℝ} (hN : 0 ≤ Nn) {h : (ι → S) → ℝ} (hh : BM h) (hv : LipBound c h (fun x => Nn * w x)) :
    LipBound c (P.avg h) (fun x => (1 - cmin * (1 - γ * E) / Fintype.card J) * (Nn * w x)) := by
  intro σ x s
  set σ' := Function.update σ x s
  set M : ℝ := (Fintype.card J : ℝ)
  have hM : (1 : ℝ) ≤ M := by
    have := (hc1.trans (hcov x)).trans (P.coverage_le_card x)
    simp only [M]
    exact_mod_cast this
  have hM0 : 0 < M := by linarith
  set cx := c (σ x) s
  have hcx : 0 ≤ cx := hc0 _ _
  set t : J → ℝ := fun j =>
    |blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ'|
  have ht_in : ∀ j, x ∈ P.block j → t j = 0 := by
    intro j hj
    simp only [t, σ', blockAvg_update_mem (P.spec_congr j) h hj σ s, sub_self, abs_zero]
  have ht_out : ∀ j, x ∉ P.block j → t j ≤ (Nn * w x + k j x σ s * (Nn * (E * w x))) * cx := by
    intro j hj
    by_cases hkz : k j x σ s = 0
    · have hm : ∀ y ∈ P.block j, Nn * w y ≤ Nn * ∑ y' ∈ P.block j, w y' := fun y hy =>
        mul_le_mul_of_nonneg_left (single_le_sum (fun y' _ => hw0 y') hy) hN
      have := lip_blockAvg_of_not_mem_at hc0 hj (hk j x σ s hj) hh hv hm
      rw [hkz, zero_mul, add_zero] at this
      rw [hkz, zero_mul, add_zero]
      exact this
    · have hm : ∀ y ∈ P.block j, Nn * w y ≤ Nn * (E * w x) := fun y hy =>
        mul_le_mul_of_nonneg_left (hwk j x y σ s hj hy hkz) hN
      exact lip_blockAvg_of_not_mem_at hc0 hj (hk j x σ s hj) hh hv hm
  have hsum : ∑ j, t j ≤ ((M - coverage P.block x) * (Nn * w x) +
      Nn * E * w x * (γ * coverage P.block x)) * cx := by
    rw [← sum_filter_add_sum_filter_not univ (fun j => x ∈ P.block j)]
    rw [sum_eq_zero (fun j hj => ht_in j (mem_filter.1 hj).2), zero_add]
    calc ∑ j ∈ univ.filter (fun j => x ∉ P.block j), t j
        ≤ ∑ j ∈ univ.filter (fun j => x ∉ P.block j), (Nn * w x + k j x σ s * (Nn * (E * w x))) * cx :=
          sum_le_sum fun j hj => ht_out j (mem_filter.1 hj).2
      _ = ((M - coverage P.block x) * (Nn * w x) +
          Nn * E * w x * ∑ j ∈ univ.filter (fun j => x ∉ P.block j), k j x σ s) * cx := by
          rw [← sum_mul, sum_add_distrib, sum_const, nsmul_eq_mul, P.card_not_mem x, mul_sum]
          congr 2
          refine sum_congr rfl fun j _ => ?_
          ring
      _ ≤ _ := by
          gcongr
          · exact mul_nonneg (mul_nonneg hN hE) (hw0 x)
          · exact hgds x σ s
  have hdiff : P.avg h σ - P.avg h σ' =
      M⁻¹ * ∑ j, (blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ') := by
    unfold avg; rw [sum_sub_distrib]; ring
  have hNw : 0 ≤ Nn * w x := mul_nonneg hN (hw0 x)
  have hcx' : (cmin : ℝ) ≤ coverage P.block x := by exact_mod_cast hcov x
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 hM0)]
  calc M⁻¹ * |∑ j, (blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ')|
      ≤ M⁻¹ * ∑ j, t j := mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (inv_nonneg.2 hM0.le)
    _ ≤ M⁻¹ * (((M - coverage P.block x) * (Nn * w x) + Nn * E * w x * (γ * coverage P.block x)) * cx) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hM0.le)
    _ = M⁻¹ * ((M - coverage P.block x * (1 - γ * E)) * (Nn * w x)) * cx := by ring
    _ ≤ M⁻¹ * ((M - cmin * (1 - γ * E)) * (Nn * w x)) * cx := by
        gcongr
    _ = (1 - cmin * (1 - γ * E) / M) * (Nn * w x) * cx := by
        field_simp

/-! ## (W-)GDS gives positive coarse Ricci curvature -/

/-- **Pointwise W-GDS ⇒ positive coarse Ricci curvature.** Under the pointwise GDS with `γ E ≤ 1` and the reach
condition on the weight `w`, the random-block heat bath `P.avg` has coarse Ricci curvature
`κ ≥ c₋ (1 - γ E) / M` for the weighted distance `d_w`. -/
theorem coarseRicci_of_gdsAt {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) (hcd : ∀ a, c a a = 0)
    (k : J → ι → (ι → S) → S → ℝ)
    (hk : ∀ j z σ s, z ∉ P.block j → IsInfluenceBoundWAt c (P.block j) (P.spec j) z σ s (k j z σ s))
    {γ : ℝ} (hgds : ∀ z σ s, ∑ j ∈ univ.filter (fun j => z ∉ P.block j), k j z σ s ≤ γ * coverage P.block z)
    {cmin : ℕ} (hcov : ∀ x, cmin ≤ coverage P.block x) (hc1 : 1 ≤ cmin)
    {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x) {E : ℝ} (hE : 0 ≤ E)
    (hwk : ∀ j x y σ s, x ∉ P.block j → y ∈ P.block j → k j x σ s ≠ 0 → w y ≤ E * w x) (hρ : γ * E ≤ 1) :
    CoarseRicciLB c w P.avg (cmin * (1 - γ * E) / Fintype.card J) := by
  intro h L hh hL0 hL
  have hv := lipBound_of_isLipW hcd hL
  have hstep := P.lipBound_avg_at hc0 k hk hgds hcov hc1 hw0 hE hwk hρ hL0 hh hv
  refine isLipW_of_lipBound (L := (1 - cmin * (1 - γ * E) / Fintype.card J) * L) ?_
  refine hstep.mono hc0 fun x => le_of_eq ?_
  ring

/-- **W-GDS ⇒ positive coarse Ricci curvature** (weighted). The hypotheses of the contraction step of Theorem A (W)
give `κ ≥ c₋ (1 - γ E) / M` for `d_w`. -/
theorem coarseRicci_of_gds {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) (hcd : ∀ a, c a a = 0) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundW c (P.block j) (P.spec j) z (k j z))
    {γ : ℝ} (hgds : GDS P.block k γ) {cmin : ℕ} (hcov : ∀ x, cmin ≤ coverage P.block x) (hc1 : 1 ≤ cmin)
    {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x) {E : ℝ} (hE : 0 ≤ E)
    (hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → k j x ≠ 0 → w y ≤ E * w x) (hρ : γ * E ≤ 1) :
    CoarseRicciLB c w P.avg (cmin * (1 - γ * E) / Fintype.card J) :=
  P.coarseRicci_of_gdsAt hc0 hcd (fun j z _ _ => k j z) (fun j z σ s hz => (hk j z hz).at σ s)
    (fun z _ _ => hgds z) hcov hc1 hw0 hE (fun j x y _ _ hx hy hk0 => hwk j x y hx hy hk0) hρ

/-- **W-GDS ⇒ positive coarse Ricci curvature, unweighted:** `κ ≥ c₋ (1 - γ) / M` for the `ℓ¹` cost distance. -/
theorem coarseRicci_of_gds_flat {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) (hcd : ∀ a, c a a = 0) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundW c (P.block j) (P.spec j) z (k j z))
    {γ : ℝ} (hgds : GDS P.block k γ) (hγ1 : γ ≤ 1) {cmin : ℕ} (hcov : ∀ x, cmin ≤ coverage P.block x)
    (hc1 : 1 ≤ cmin) :
    CoarseRicciLB c (fun _ => (1 : ℝ)) P.avg (cmin * (1 - γ) / Fintype.card J) := by
  have := P.coarseRicci_of_gds hc0 hcd k hk hgds hcov hc1 (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    zero_le_one (fun _ _ _ _ _ _ => by norm_num) (by linarith)
  simpa using this

/-! ## The normalisation is sharp: `κ ≤ c(x)/M` -/

/-- **Upper bound on the curvature.** If `P.avg` has coarse Ricci curvature `≥ κ` for the unweighted distance, then for
every index `x`, every 1-Lipschitz (for `c`) bounded measurable `φ : S → ℝ` and all `a, s`:
`(1 - c(x)/M) |φ(a) - φ(s)| ≤ (1 - κ) c(a, s)`. With `φ = c(·, s)` (if `c` is a metric) and `c(a, s) > 0`, this gives
`κ ≤ c(x)/M`: a block that contains `x` forgets `x` completely, the others keep it. -/
theorem coarseRicci_le_coverage [Nonempty J] {c : S → S → ℝ} (hcd : ∀ a, c a a = 0) {κ : ℝ}
    (hK : CoarseRicciLB c (fun _ => (1 : ℝ)) P.avg κ) (x : ι) {φ : S → ℝ} (hφm : Measurable φ)
    (hφb : ∃ C, ∀ a, |φ a| ≤ C) (hφL : ∀ a b, |φ a - φ b| ≤ c a b) (σ : ι → S) (s : S) :
    (1 - (coverage P.block x : ℝ) / Fintype.card J) * |φ (σ x) - φ s| ≤ (1 - κ) * c (σ x) s := by
  set h : (ι → S) → ℝ := fun τ => φ (τ x)
  have hh : BM h := by
    obtain ⟨C, hC⟩ := hφb
    exact ⟨hφm.comp (measurable_pi_apply x), ⟨C, fun τ => hC _⟩⟩
  have hLip : IsLipW c (fun _ => (1 : ℝ)) h 1 := by
    refine isLipW_of_lipBound ?_
    intro τ y t
    by_cases hy : y = x
    · rw [hy]
      simp only [h, Function.update_self]
      simpa using hφL (τ x) t
    · simp only [h, Function.update_of_ne (Ne.symm hy), sub_self, abs_zero]
      have : (0 : ℝ) ≤ c (τ y) t := by
        have := hφL (τ y) t
        exact (abs_nonneg _).trans this
      simpa using this
  have hres := hK h 1 hh zero_le_one hLip σ (Function.update σ x s)
  rw [wdist_update c hcd] at hres
  -- compute `P.avg h σ - P.avg h σ^x`
  set M : ℝ := (Fintype.card J : ℝ)
  have hin : ∀ j, x ∈ P.block j →
      blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h (Function.update σ x s) = 0 := by
    intro j hj
    rw [blockAvg_update_mem (P.spec_congr j) h hj σ s, sub_self]
  have hout : ∀ j, x ∉ P.block j → ∀ τ : ι → S, blockAvg (P.block j) (P.spec j) h τ = φ (τ x) := by
    intro j hj τ
    unfold blockAvg
    simp only [h, splice_of_not_mem hj]
    simp
  have hdiff : P.avg h σ - P.avg h (Function.update σ x s) = M⁻¹ * ((M - coverage P.block x) * (φ (σ x) - φ s)) := by
    unfold avg
    rw [← mul_sub, ← sum_sub_distrib, ← sum_filter_add_sum_filter_not univ (fun j => x ∈ P.block j)]
    rw [sum_eq_zero (fun j hj => hin j (mem_filter.1 hj).2), zero_add]
    have hs : ∑ j ∈ univ.filter (fun j => x ∉ P.block j),
        (blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h (Function.update σ x s)) =
        ∑ j ∈ univ.filter (fun j => x ∉ P.block j), (φ (σ x) - φ s) := by
      refine sum_congr rfl fun j hj => ?_
      rw [hout j (mem_filter.1 hj).2 σ, hout j (mem_filter.1 hj).2 (Function.update σ x s),
        Function.update_self]
    rw [hs, sum_const, nsmul_eq_mul, P.card_not_mem x]
  have hM0 : 0 < M := by
    simp only [M]
    exact_mod_cast Fintype.card_pos
  have hcovM : (coverage P.block x : ℝ) ≤ M := by simp only [M]; exact_mod_cast P.coverage_le_card x
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 hM0), abs_mul, abs_of_nonneg (sub_nonneg.2 hcovM)] at hres
  have e : (1 - (coverage P.block x : ℝ) / M) * |φ (σ x) - φ s| =
      M⁻¹ * ((M - coverage P.block x) * |φ (σ x) - φ s|) := by
    field_simp
  rw [e]
  refine hres.trans (le_of_eq ?_)
  simp

end BlockSpec

end OneScale
