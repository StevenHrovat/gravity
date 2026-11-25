/-
The one-scale reduction, abstract layer (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §1.5 (L_x), §1.6 (k^W), Lemma 2.5 (W), Theorem A (W).
-/

import OneScale.Decay

/-!
# Theorem A, W variant (per-link Lipschitz observables)

A cost `c : S → S → ℝ` with `0 ≤ c ≤ D_c` (the note's bi-invariant metric `ρ` with `diam_ρ(G) ≤ D_c`; the proofs use
only nonnegativity and the bound, not the metric axioms).

* `LipBound c h v`: `|h σ - h σ'| ≤ v x · c(σ_x, σ'_x)` when `σ, σ'` differ only at `x` (the note's `L_x(h) ≤ v x`).
* `IsInfluenceBoundW c B q z k`: the dual W coefficient in homogeneous form (§1.6):
  `|q^σ(F) - q^{σ'}(F)| ≤ k L c(σ_z, σ'_z)` for `F` depending on `B` with `L_y(F) ≤ L` on `B`.
* `lip_blockAvg_of_not_mem`: **Lemma 2.5 (W)**; `BlockSpec.lipBound_avg`: the contraction step for `L_x`.
* `BlockSpec.theoremA_W`: **Theorem A (W)**: for `f` bounded with `δ_a(f) ≤ v_a` on its support `A` and `g` with
  `L_x(g) ≤ L_g` on its support `S_g`,
  `|Cov(f, g)| ≤ b D_c/(c₋(1 - ρ_λ)) · (c₊ ∑_{a ∈ A} v_a) · L_g · e^{-λ(R - D₀)}`.
The W-GDS uses the W coefficients; everything else is as in the H variant (`OneScale.Decay`).
-/

open MeasureTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale

variable {ι S : Type*} [Fintype ι] [DecidableEq ι]

/-- `L_x(h) ≤ v x` for the cost `c`. -/
def LipBound (c : S → S → ℝ) (h : (ι → S) → ℝ) (v : ι → ℝ) : Prop :=
  ∀ (σ : ι → S) (x : ι) (s : S), |h σ - h (Function.update σ x s)| ≤ v x * c (σ x) s

/-- A Lipschitz bound with a bounded cost is an oscillation bound: `δ_x(h) ≤ D_c L_x(h)`. -/
theorem LipBound.oscBound {c : S → S → ℝ} {h : (ι → S) → ℝ} {v : ι → ℝ} (hv : LipBound c h v)
    (hv0 : ∀ x, 0 ≤ v x) {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc) : OscBound h (fun x => v x * Dc) :=
  fun σ x s => (hv σ x s).trans (mul_le_mul_of_nonneg_left (hcD _ _) (hv0 x))

theorem LipBound.mono {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {h : (ι → S) → ℝ} {v v' : ι → ℝ}
    (hv : LipBound c h v) (hle : ∀ x, v x ≤ v' x) : LipBound c h v' :=
  fun σ x s => (hv σ x s).trans (mul_le_mul_of_nonneg_right (hle x) (hc0 _ _))

variable [MeasurableSpace S]

/-- **Boundary-influence coefficient, W variant, homogeneous dual form** (note §1.6). -/
def IsInfluenceBoundW (c : S → S → ℝ) (B : Finset ι) (q : (ι → S) → Measure (ι → S)) (z : ι) (k : ℝ) : Prop :=
  ∀ (σ : ι → S) (s : S) (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B →
    (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L * c (ξ y) t) →
    |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q (Function.update σ z s))| ≤ k * L * c (σ z) s

/-- **Lemma 2.5 (W), one block, `x` outside the block.** -/
theorem lip_blockAvg_of_not_mem {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {B : Finset ι}
    {q : (ι → S) → Measure (ι → S)} [∀ σ, IsProbabilityMeasure (q σ)] {x : ι} (hx : x ∉ B) {k : ℝ}
    (hk : IsInfluenceBoundW c B q x k) {h : (ι → S) → ℝ} (hh : BM h) {v : ι → ℝ} (hv : LipBound c h v)
    {m : ℝ} (hm : ∀ y ∈ B, v y ≤ m) (σ : ι → S) (s : S) :
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
  have h2 := hk σ s F m hF hFdep hFosc
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

/-- **Step 1 of Theorem A (W): contraction of the Lipschitz bounds.** -/
theorem lipBound_avg {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundW c (P.block j) (P.spec j) z (k j z))
    {γ : ℝ} (hgds : GDS P.block k γ) {cmin : ℕ} (hcov : ∀ x, cmin ≤ coverage P.block x) (hc1 : 1 ≤ cmin)
    {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x) {E : ℝ} (hE : 0 ≤ E)
    (hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → k j x ≠ 0 → w y ≤ E * w x) (hρ : γ * E ≤ 1)
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
  have ht_out : ∀ j, x ∉ P.block j → t j ≤ (Nn * w x + k j x * (Nn * (E * w x))) * cx := by
    intro j hj
    by_cases hkz : k j x = 0
    · have hm : ∀ y ∈ P.block j, Nn * w y ≤ Nn * ∑ y' ∈ P.block j, w y' := fun y hy =>
        mul_le_mul_of_nonneg_left (single_le_sum (fun y' _ => hw0 y') hy) hN
      have := lip_blockAvg_of_not_mem hc0 hj (hk j x hj) hh hv hm σ s
      rw [hkz, zero_mul, add_zero] at this
      rw [hkz, zero_mul, add_zero]
      exact this
    · have hm : ∀ y ∈ P.block j, Nn * w y ≤ Nn * (E * w x) := fun y hy =>
        mul_le_mul_of_nonneg_left (hwk j x y hj hy hkz) hN
      exact lip_blockAvg_of_not_mem hc0 hj (hk j x hj) hh hv hm σ s
  have hsum : ∑ j, t j ≤ ((M - coverage P.block x) * (Nn * w x) +
      Nn * E * w x * (γ * coverage P.block x)) * cx := by
    rw [← sum_filter_add_sum_filter_not univ (fun j => x ∈ P.block j)]
    rw [sum_eq_zero (fun j hj => ht_in j (mem_filter.1 hj).2), zero_add]
    calc ∑ j ∈ univ.filter (fun j => x ∉ P.block j), t j
        ≤ ∑ j ∈ univ.filter (fun j => x ∉ P.block j), (Nn * w x + k j x * (Nn * (E * w x))) * cx :=
          sum_le_sum fun j hj => ht_out j (mem_filter.1 hj).2
      _ = ((M - coverage P.block x) * (Nn * w x) +
          Nn * E * w x * ∑ j ∈ univ.filter (fun j => x ∉ P.block j), k j x) * cx := by
          rw [← sum_mul, sum_add_distrib, sum_const, nsmul_eq_mul, P.card_not_mem x, mul_sum]
          congr 2
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

/-- **Theorem A (W), core estimate with an abstract weight.** -/
theorem cov_le_weighted_W [IsProbabilityMeasure μ] [Nonempty ι] {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b)
    {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundW c (P.block j) (P.spec j) z (k j z))
    {γ : ℝ} (hγ : 0 ≤ γ) (hgds : GDS P.block k γ) {cmin : ℕ} (hc1 : 1 ≤ cmin)
    (hcov : ∀ x, cmin ≤ coverage P.block x)
    {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x) {E : ℝ} (hE : 0 ≤ E)
    (hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → k j x ≠ 0 → w y ≤ E * w x) (hρ : γ * E < 1)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A : Finset ι} (hfA : DepOn f A) {vf : ι → ℝ}
    (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : LipBound c g (fun x => Lg * w x)) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      Lg * Dc / (cmin * (1 - γ * E)) * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty ι)
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure μ
  set M : ℝ := (Fintype.card J : ℝ)
  have hMc : cmin ≤ Fintype.card J := (hcov x₀).trans (P.coverage_le_card x₀)
  have hJ : Nonempty J := Fintype.card_pos_iff.1 (by omega)
  have hM0 : 0 < M := by simp only [M]; exact_mod_cast (by omega : 0 < Fintype.card J)
  have hcm : (1 : ℝ) ≤ cmin := by exact_mod_cast hc1
  have hcM : (cmin : ℝ) ≤ M := by simp only [M]; exact_mod_cast hMc
  have hγE0 : 0 ≤ γ * E := mul_nonneg hγ hE
  have hgap : 0 < 1 - γ * E := by linarith
  have hDc : 0 ≤ Dc := (hc0 (σ₀ x₀) (σ₀ x₀)).trans (hcD _ _)
  set θ : ℝ := 1 - cmin * (1 - γ * E) / M with hθ
  have hθ1 : θ < 1 := by
    have : 0 < cmin * (1 - γ * E) / M := div_pos (mul_pos (by linarith) hgap) hM0
    linarith
  have hθ0 : 0 ≤ θ := by
    have : cmin * (1 - γ * E) / M ≤ 1 := by
      rw [div_le_one hM0]
      nlinarith
    linarith
  -- Step 1 for Lipschitz bounds, then convert to oscillation bounds
  have hlip : ∀ t, LipBound c (P.iter g t) (fun x => θ ^ t * Lg * w x) := by
    intro t
    induction t with
    | zero => simpa [iter_zero] using hvg
    | succ t ih =>
      rw [iter_succ]
      have h := P.lipBound_avg hc0 k hk hgds hcov hc1 hw0 hE hwk hρ.le (Nn := θ ^ t * Lg)
        (mul_nonneg (pow_nonneg hθ0 t) hLg) (P.bm_iter hg t) (by simpa [mul_assoc] using ih)
      refine h.mono hc0 fun x => le_of_eq ?_
      rw [pow_succ]; ring
  have hosc : ∀ t, OscBound (P.iter g t) (fun x => θ ^ t * (Lg * Dc) * w x) := by
    intro t
    refine ((hlip t).oscBound (fun x => mul_nonneg (mul_nonneg (pow_nonneg hθ0 t) hLg) (hw0 x)) hcD).mono
      fun x => le_of_eq ?_
    ring
  have hD0 : 0 < (cmin : ℝ) * (1 - γ * E) := mul_pos (by linarith) hgap
  exact P.cov_le_of_iter_osc hθ0 hθ1 hD0 (by simp only [θ, M]; field_simp; ring) hw0 hf hg hfA hvf
    (mul_nonneg hLg hDc) hosc

/-- **Theorem A (W variant)** (`PROOF-NOTE.md` §4.1). As `theoremA_H`, with `g` per-link Lipschitz
(`L_x(g) ≤ L_g` for the cost `c ≤ D_c`) and W influence coefficients:
`|μ(f g) - μ(f) μ(g)| ≤ b D_c/(c₋(1 - ρ_λ)) · (c₊ ∑_{a ∈ A} v_a) · L_g · e^{-λ(R - D₀)}`. -/
theorem theoremA_W [IsProbabilityMeasure μ] [Nonempty ι] {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b)
    {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundW c (P.block j) (P.spec j) z (k j z))
    {γ : ℝ} (hγ : 0 ≤ γ) (hgds : GDS P.block k γ) {cmin cmax b : ℕ} (hc1 : 1 ≤ cmin)
    (hcov : ∀ x, cmin ≤ coverage P.block x) (hcmax : ∀ x, coverage P.block x ≤ cmax)
    (hb : ∀ j, (P.block j).card ≤ b)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {D₀ D₁ : ℝ} (hD₀ : ∀ j, ∀ x ∈ P.block j, ∀ y ∈ P.block j, dist x y ≤ D₀)
    (hD₁ : ∀ j x y, x ∉ P.block j → y ∈ P.block j → k j x ≠ 0 → dist x y ≤ D₁)
    {lam : ℝ} (hlam : 0 ≤ lam) (hρ : γ * Real.exp (lam * D₁) < 1)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A) (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : LipBound c g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      b * Dc / (cmin * (1 - γ * Real.exp (lam * D₁))) * (cmax * ∑ a ∈ A, vf a) * Lg *
        Real.exp (-(lam * (R - D₀))) := by
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure μ
  obtain ⟨x₀⟩ := (inferInstance : Nonempty ι)
  have hDc : 0 ≤ Dc := (hc0 (σ₀ x₀) (σ₀ x₀)).trans (hcD _ _)
  set w := expWeight dist lam Sg
  set E := Real.exp (lam * D₁)
  set e := Real.exp (-(lam * (R - D₀)))
  have hw0 : ∀ x, 0 ≤ w x := expWeight_nonneg dist lam Sg
  have hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → k j x ≠ 0 → w y ≤ E * w x := by
    intro j x y hx hy hkx
    refine (expWeight_le_mul dist htri hlam Sg x y).trans (mul_le_mul_of_nonneg_right ?_ (hw0 x))
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hD₁ j x y hx hy hkx) hlam)
  have hvg' : LipBound c g (fun x => Lg * w x) := by
    intro σ x s
    by_cases hx : x ∈ Sg
    · calc |g σ - g (Function.update σ x s)| ≤ Lg * c (σ x) s := hvg σ x s
        _ = Lg * 1 * c (σ x) s := by ring
        _ ≤ Lg * w x * c (σ x) s := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (one_le_expWeight dist hd0 lam hx) hLg) (hc0 _ _)
    · rw [hgS.update_eq hx σ s, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hLg (hw0 x)) (hc0 _ _)
  have hcore := P.cov_le_weighted_W hc0 hcD k hk hγ hgds hc1 hcov hw0 (Real.exp_pos _).le hwk hρ hf hg hfA hvf
    hLg hvg'
  refine hcore.trans ?_
  have hvf0 : ∀ a, 0 ≤ vf a := fun a => hvf.nonneg σ₀ a
  have hgap : 0 < 1 - γ * E := by linarith
  have hpre : 0 ≤ Lg * Dc / (cmin * (1 - γ * E)) :=
    div_nonneg (mul_nonneg hLg hDc) (mul_nonneg (Nat.cast_nonneg _) hgap.le)
  have hblock : ∀ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y ≤
      (∑ a ∈ P.block j ∩ A, vf a) * (b * e) := by
    intro j
    by_cases hj : (P.block j ∩ A).Nonempty
    · obtain ⟨a, ha⟩ := hj
      refine mul_le_mul_of_nonneg_left ?_ (sum_nonneg fun a _ => hvf0 a)
      have hwy : ∀ y ∈ P.block j, w y ≤ e := fun y hy =>
        expWeight_le_of_dist dist htri hlam (hR a (mem_inter.1 ha).2)
          (hD₀ j a (mem_inter.1 ha).1 y hy)
      calc ∑ y ∈ P.block j, w y ≤ ∑ _y ∈ P.block j, e := sum_le_sum hwy
        _ = (P.block j).card * e := by rw [sum_const, nsmul_eq_mul]
        _ ≤ b * e := mul_le_mul_of_nonneg_right (by exact_mod_cast hb j) (Real.exp_pos _).le
    · rw [not_nonempty_iff_eq_empty.1 hj, sum_empty, zero_mul, zero_mul]
  have hsum : ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y ≤
      (cmax * ∑ a ∈ A, vf a) * (b * e) := by
    refine (sum_le_sum fun j _ => hblock j).trans ?_
    rw [← sum_mul, P.sum_sum_inter A vf]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
    rw [mul_sum]
    exact sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hcmax a) (hvf0 a)
  calc Lg * Dc / (cmin * (1 - γ * E)) * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y
      ≤ Lg * Dc / (cmin * (1 - γ * E)) * ((cmax * ∑ a ∈ A, vf a) * (b * e)) :=
        mul_le_mul_of_nonneg_left hsum hpre
    _ = b * Dc / (cmin * (1 - γ * E)) * (cmax * ∑ a ∈ A, vf a) * Lg * e := by ring

end BlockSpec

end OneScale
