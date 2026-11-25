/-
Proof phase, cycle 5, workstream 3 (c5c-repair): the weighted W₁ Theorem A and `LevelDprimeW` without a finite range
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5c-repair/NOTE.md`, section 1.
-/

import ProofPhase.V3.W1Route
import Attempts.R3.TailDecay

/-!
# Weighted W₁ Dobrushin theorem; D′ in W₁ form with exponential tails

The review `c4-fable/REVIEW.md` §1.1: `V3.LevelDprimeW` asks the W₁ influence coefficients to vanish beyond a fixed range
`D₁` (uniform in level and volume), i.e. that the blocked law is an exact finite-range Markov field. A blocked Wilson law has
an effective action with tails at every distance, so that clause is out of reach of the true theory.

This file removes it. The influence coefficients may be nonzero at every distance; the condition is on **exponentially
weighted column sums** (the W₁ form of the weighted Dobrushin condition, Dobrushin 1970, Gross 1979):

  `∑_{i ≠ z} k(i, z) e^{λ d(z, i)} ≤ γ < 1`.

* `lipBound_avg_w`, `cov_le_weighted_Ww`, **`theoremA_Ww`** (S): Theorem A, W variant (`g` Lipschitz for the cost `c`),
  under the weighted block condition `Attempts.R3.GDSw` with weights `e^{λ E_j(x)}`. Line-by-line merge of
  `OneScale.BlockSpec.theoremA_W` (W bookkeeping) and `Attempts.R3.theoremA_w` (weighted bookkeeping).
* **`decay_of_siteWw`** (S): the single-site form (the weighted `Certified.decay_of_siteW`): the bound
  `|Cov(f, g)| ≤ D_c/(1 − γ) (∑ v_a) L_g e^{−λR}`. No range, no `D₁`.
* `weightedColumn_le_of_range` (S): a finite-range column `≤ γ` with nonnegative coefficients has weighted column
  `≤ γ e^{λ D₁}`, so the old hypothesis is a special case.
* `siteInfluenceW_nonneg`, `exists_geodSU2_pos` (S): W₁ influence coefficients for the geodesic cost on SU(2) are
  automatically nonnegative (needed for the special-case statement).
* **`LevelDprimeWw T B λ`** (named hypothesis, open; replaces `V3.LevelDprimeW`): from some level on, in every volume,
  the blocked law is the Gibbs measure of a bounded coarse potential whose single-link W₁ influences have weighted
  column sums `≤ γ < 1` (weight `e^{λ · linkDist}`). **`blockGapUnifW_of_levelDprimeWw`** (S): it gives
  `V3.BlockGapUnifW T B λ` with constant `π/(1 − γ)`.
* **`levelDprimeWw_of_levelDprimeW`** (S): the old hypothesis implies the new one at the same rate (with
  `γ' = γ e^{λ D₁}`), so every theorem proved from `LevelDprimeW` stays available through `LevelDprimeWw`.
* `LevelDprimeWw.mono` (S): the condition at rate `λ` gives it at every smaller rate `0 ≤ λ' ≤ λ`.

**Claim level.** Everything here is proved (no `sorry`, no new axiom). The weighted theorem is standard (substantive in
Lean, not new mathematics). `LevelDprimeWw` is an open named hypothesis of the same strength as before minus the
finite-range clause: it is the W₁ D′ condition for the true blocked law, i.e. strategy (a) of blueprint v4 §3.3 for IR.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.LinkDist ProofPhase.Certified

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Repair

/-! ## 1. Theorem A (W) under a weighted Dobrushin condition -/

section Generic

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {J : Type*} [Fintype J]
variable {μ : Measure (ι → S)} (P : BlockSpec μ J)

/-- **Step 1 under the weighted condition, W variant.** If `L_x(h) ≤ N w(x)`, `w(y) ≤ e_j(x) w(x)` for `x ∉ B_j ∋ y`,
and `GDSw` holds with `γ ≤ 1`, then `L_x(P h) ≤ (1 − c₋(1 − γ)/M) N w(x)`. -/
theorem lipBound_avg_w {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundW c (P.block j) (P.spec j) z (k j z))
    (e : J → ι → ℝ) {γ : ℝ} (hgds : Attempts.R3.GDSw P.block k e γ) {cmin : ℕ}
    (hcov : ∀ x, cmin ≤ coverage P.block x) (hc1 : 1 ≤ cmin) {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → w y ≤ e j x * w x) (hγ1 : γ ≤ 1)
    {Nn : ℝ} (hN : 0 ≤ Nn) {h : (ι → S) → ℝ} (hh : BM h) (hv : LipBound c h (fun x => Nn * w x)) :
    LipBound c (P.avg h) (fun x => (1 - cmin * (1 - γ) / Fintype.card J) * (Nn * w x)) := by
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
  have ht_out : ∀ j, x ∉ P.block j → t j ≤ (Nn * w x + k j x * (Nn * (e j x * w x))) * cx := by
    intro j hj
    have hm : ∀ y ∈ P.block j, Nn * w y ≤ Nn * (e j x * w x) := fun y hy =>
      mul_le_mul_of_nonneg_left (hwk j x y hj hy) hN
    exact lip_blockAvg_of_not_mem hc0 hj (hk j x hj) hh hv hm σ s
  have hNw : 0 ≤ Nn * w x := mul_nonneg hN (hw0 x)
  have hsum : ∑ j, t j ≤ ((M - coverage P.block x) * (Nn * w x) +
      Nn * w x * (γ * coverage P.block x)) * cx := by
    rw [← sum_filter_add_sum_filter_not univ (fun j => x ∈ P.block j)]
    rw [sum_eq_zero (fun j hj => ht_in j (mem_filter.1 hj).2), zero_add]
    calc ∑ j ∈ univ.filter (fun j => x ∉ P.block j), t j
        ≤ ∑ j ∈ univ.filter (fun j => x ∉ P.block j), (Nn * w x + k j x * (Nn * (e j x * w x))) * cx :=
          sum_le_sum fun j hj => ht_out j (mem_filter.1 hj).2
      _ = ((M - coverage P.block x) * (Nn * w x) +
          Nn * w x * ∑ j ∈ univ.filter (fun j => x ∉ P.block j), k j x * e j x) * cx := by
          rw [← sum_mul, sum_add_distrib, sum_const, nsmul_eq_mul, P.card_not_mem x, mul_sum]
          congr 2
          refine sum_congr rfl fun j _ => ?_
          ring
      _ ≤ _ := by
          gcongr
          exact hgds x
  have hdiff : P.avg h σ - P.avg h σ' =
      M⁻¹ * ∑ j, (blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ') := by
    unfold BlockSpec.avg; rw [sum_sub_distrib]; ring
  have hcx' : (cmin : ℝ) ≤ coverage P.block x := by exact_mod_cast hcov x
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 hM0)]
  calc M⁻¹ * |∑ j, (blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ')|
      ≤ M⁻¹ * ∑ j, t j := mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (inv_nonneg.2 hM0.le)
    _ ≤ M⁻¹ * (((M - coverage P.block x) * (Nn * w x) + Nn * w x * (γ * coverage P.block x)) * cx) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hM0.le)
    _ = M⁻¹ * ((M - coverage P.block x * (1 - γ)) * (Nn * w x)) * cx := by ring
    _ ≤ M⁻¹ * ((M - cmin * (1 - γ)) * (Nn * w x)) * cx := by
        gcongr
    _ = (1 - cmin * (1 - γ) / M) * (Nn * w x) * cx := by
        field_simp

/-- **The core estimate under the weighted condition, W variant.** -/
theorem cov_le_weighted_Ww [IsProbabilityMeasure μ] [Nonempty ι] {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b)
    {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundW c (P.block j) (P.spec j) z (k j z))
    (e : J → ι → ℝ) {γ : ℝ} (hγ : 0 ≤ γ) (hgds : Attempts.R3.GDSw P.block k e γ) {cmin : ℕ} (hc1 : 1 ≤ cmin)
    (hcov : ∀ x, cmin ≤ coverage P.block x) {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → w y ≤ e j x * w x) (hρ : γ < 1)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A : Finset ι} (hfA : DepOn f A) {vf : ι → ℝ}
    (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : LipBound c g (fun x => Lg * w x)) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      Lg * Dc / (cmin * (1 - γ)) * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty ι)
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure μ
  set M : ℝ := (Fintype.card J : ℝ)
  have hMc : cmin ≤ Fintype.card J := (hcov x₀).trans (P.coverage_le_card x₀)
  have hJ : Nonempty J := Fintype.card_pos_iff.1 (by omega)
  have hM0 : 0 < M := by simp only [M]; exact_mod_cast (by omega : 0 < Fintype.card J)
  have hcm : (1 : ℝ) ≤ cmin := by exact_mod_cast hc1
  have hcM : (cmin : ℝ) ≤ M := by simp only [M]; exact_mod_cast hMc
  have hgap : 0 < 1 - γ := by linarith
  have hDc : 0 ≤ Dc := (hc0 (σ₀ x₀) (σ₀ x₀)).trans (hcD _ _)
  set θ : ℝ := 1 - cmin * (1 - γ) / M with hθ
  have hθ1 : θ < 1 := by
    have : 0 < cmin * (1 - γ) / M := div_pos (mul_pos (by linarith) hgap) hM0
    linarith
  have hθ0 : 0 ≤ θ := by
    have : cmin * (1 - γ) / M ≤ 1 := by
      rw [div_le_one hM0]
      nlinarith
    linarith
  have hlip : ∀ t, LipBound c (P.iter g t) (fun x => θ ^ t * Lg * w x) := by
    intro t
    induction t with
    | zero => simpa [BlockSpec.iter_zero] using hvg
    | succ t ih =>
      rw [BlockSpec.iter_succ]
      have h := lipBound_avg_w P hc0 k hk e hgds hcov hc1 hw0 hwk hρ.le (Nn := θ ^ t * Lg)
        (mul_nonneg (pow_nonneg hθ0 t) hLg) (P.bm_iter hg t) (by simpa [mul_assoc] using ih)
      refine h.mono hc0 fun x => le_of_eq ?_
      rw [pow_succ]; ring
  have hosc : ∀ t, OscBound (P.iter g t) (fun x => θ ^ t * (Lg * Dc) * w x) := by
    intro t
    refine ((hlip t).oscBound (fun x => mul_nonneg (mul_nonneg (pow_nonneg hθ0 t) hLg) (hw0 x)) hcD).mono
      fun x => le_of_eq ?_
    ring
  have hD0 : 0 < (cmin : ℝ) * (1 - γ) := mul_pos (by linarith) hgap
  exact P.cov_le_of_iter_osc hθ0 hθ1 hD0 (by simp only [θ, M]; field_simp; ring) hw0 hf hg hfA hvf
    (mul_nonneg hLg hDc) hosc

/-- **Theorem A (W) with a weighted Dobrushin condition (no finite range).** Let `E_j(x)` bound `dist(x, y)` for
`x ∉ B_j ∋ y`, `λ ≥ 0`, and `∑_{j : x ∉ B_j} k_j(x) e^{λ E_j(x)} ≤ γ c(x)` with `0 ≤ γ < 1` (W₁ coefficients). Then
`|μ(f g) − μ(f) μ(g)| ≤ b D_c/(c₋(1 − γ)) · (c₊ ∑_{a ∈ A} v_a) · L_g · e^{−λ(R − D₀)}`. -/
theorem theoremA_Ww [IsProbabilityMeasure μ] [Nonempty ι] {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b)
    {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundW c (P.block j) (P.spec j) z (k j z))
    {cmin cmax b : ℕ} (hc1 : 1 ≤ cmin)
    (hcov : ∀ x, cmin ≤ coverage P.block x) (hcmax : ∀ x, coverage P.block x ≤ cmax)
    (hb : ∀ j, (P.block j).card ≤ b)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {D₀ : ℝ} (hD₀ : ∀ j, ∀ x ∈ P.block j, ∀ y ∈ P.block j, dist x y ≤ D₀)
    (E : J → ι → ℝ) (hE : ∀ j x y, x ∉ P.block j → y ∈ P.block j → dist x y ≤ E j x)
    {lam : ℝ} (hlam : 0 ≤ lam) {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hgds : Attempts.R3.GDSw P.block k (fun j x => Real.exp (lam * E j x)) γ)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A) (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : LipBound c g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      b * Dc / (cmin * (1 - γ)) * (cmax * ∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * (R - D₀))) := by
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure μ
  obtain ⟨x₀⟩ := (inferInstance : Nonempty ι)
  have hDc : 0 ≤ Dc := (hc0 (σ₀ x₀) (σ₀ x₀)).trans (hcD _ _)
  set w := expWeight dist lam Sg
  set e := Real.exp (-(lam * (R - D₀)))
  have hw0 : ∀ x, 0 ≤ w x := expWeight_nonneg dist lam Sg
  have hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → w y ≤ Real.exp (lam * E j x) * w x := by
    intro j x y hx hy
    refine (expWeight_le_mul dist htri hlam Sg x y).trans (mul_le_mul_of_nonneg_right ?_ (hw0 x))
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hE j x y hx hy) hlam)
  have hvg' : LipBound c g (fun x => Lg * w x) := by
    intro σ x s
    by_cases hx : x ∈ Sg
    · calc |g σ - g (Function.update σ x s)| ≤ Lg * c (σ x) s := hvg σ x s
        _ = Lg * 1 * c (σ x) s := by ring
        _ ≤ Lg * w x * c (σ x) s := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (one_le_expWeight dist hd0 lam hx) hLg) (hc0 _ _)
    · rw [hgS.update_eq hx σ s, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hLg (hw0 x)) (hc0 _ _)
  have hcore := cov_le_weighted_Ww P hc0 hcD k hk (fun j x => Real.exp (lam * E j x)) hγ hgds hc1 hcov hw0 hwk
    hγ1 hf hg hfA hvf hLg hvg'
  refine hcore.trans ?_
  have hvf0 : ∀ a, 0 ≤ vf a := fun a => hvf.nonneg σ₀ a
  have hgap : 0 < 1 - γ := by linarith
  have hpre : 0 ≤ Lg * Dc / (cmin * (1 - γ)) :=
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
  calc Lg * Dc / (cmin * (1 - γ)) * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y
      ≤ Lg * Dc / (cmin * (1 - γ)) * ((cmax * ∑ a ∈ A, vf a) * (b * e)) :=
        mul_le_mul_of_nonneg_left hsum hpre
    _ = b * Dc / (cmin * (1 - γ)) * (cmax * ∑ a ∈ A, vf a) * Lg * e := by ring

end Generic

/-! ## 2. Single sites: the weighted `decay_of_siteW` -/

section Site

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {X : Type*} [Fintype X]
  (ν : Measure S) [IsProbabilityMeasure ν]

/-- **The weighted W₁ column condition for single sites:** `∑_{i ≠ z} k(i, z) e^{λ d(z, i)} ≤ γ` for every `z`. -/
def WeightedColumnW (k : ι → ι → ℝ) (dist : ι → ι → ℝ) (lam γ : ℝ) : Prop :=
  ∀ z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), k i z * Real.exp (lam * dist z i) ≤ γ

/-- **Dobrushin's theorem with W₁ coefficients for single sites, weighted (no finite range).** If the single-link W₁
influences have weighted column sums `≤ γ < 1` at rate `λ ≥ 0`, then
`|Cov(f, g)| ≤ D_c/(1 − γ) (∑ v_a) L_g e^{−λR}` for `f` bounded and `g` Lipschitz at distance `≥ R`. -/
theorem decay_of_siteWw [Nonempty ι] {supp : X → Finset ι} {V : X → (ι → S) → ℝ}
    (hV : Attempts.R3.Potential supp V) {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc)
    {k : ι → ι → ℝ} (hk : SiteInfluenceW ν supp V c k)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {lam : ℝ} (hlam : 0 ≤ lam) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hcol : WeightedColumnW k dist lam γ)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A) (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : LipBound c g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂(Attempts.R3.gibbsMeasure ν V) -
        (∫ σ, f σ ∂(Attempts.R3.gibbsMeasure ν V)) * ∫ σ, g σ ∂(Attempts.R3.gibbsMeasure ν V)| ≤
      Dc / (1 - γ) * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  have := Attempts.R3.isProbabilityMeasure_gibbsMeasure ν hV
  set P := Attempts.R3.factorSpec ν supp V hV
  have hk' : ∀ j z, z ∉ P.block j → IsInfluenceBoundW c (P.block j) (P.spec j) z (k j z) := by
    intro j z hz
    rw [Attempts.R3.factorSpec_block] at hz ⊢
    rw [Attempts.R3.factorSpec_spec]
    exact hk j z hz
  have hcov : ∀ x, coverage P.block x = 1 := Attempts.R3.coverage_singleton
  have hgds : Attempts.R3.GDSw P.block k (fun j x => Real.exp (lam * dist x j)) γ := by
    intro z
    rw [hcov z, Nat.cast_one, mul_one]
    exact hcol z
  have h := theoremA_Ww P hc0 hcD k hk' (cmin := 1) (cmax := 1) (b := 1) le_rfl
    (fun x => (hcov x).ge) (fun x => (hcov x).le) (fun j => by simp [P, Attempts.R3.factorSpec_block])
    dist hd0 htri (D₀ := 0)
    (fun j x hx y hy => by
      simp only [P, Attempts.R3.factorSpec_block, mem_singleton] at hx hy
      rw [hx, hy, hd0])
    (fun j x => dist x j)
    (fun j x y hx hy => by
      simp only [P, Attempts.R3.factorSpec_block, mem_singleton] at hy
      rw [hy])
    hlam hγ0 hγ1 hgds hf hg hfA hgS hvf hLg hvg hR
  refine h.trans (le_of_eq ?_)
  simp only [Nat.cast_one, one_mul, sub_zero]

/-- **A finite-range column is a weighted column** (nonnegative coefficients): `∑ k ≤ γ` and `k(i, z) ≠ 0 ⇒
d(z, i) ≤ D₁` give `∑ k(i, z) e^{λ d(z, i)} ≤ γ e^{λ D₁}`. -/
theorem weightedColumn_le_of_range {k : ι → ι → ℝ} (hk0 : ∀ i z, z ∉ ({i} : Finset ι) → 0 ≤ k i z)
    (dist : ι → ι → ℝ) {lam γ D₁ : ℝ} (hlam : 0 ≤ lam)
    (hcol : ∀ z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), k i z ≤ γ)
    (hD₁ : ∀ i z, z ∉ ({i} : Finset ι) → k i z ≠ 0 → dist z i ≤ D₁) :
    WeightedColumnW k dist lam (γ * Real.exp (lam * D₁)) := by
  intro z
  calc ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), k i z * Real.exp (lam * dist z i)
      ≤ ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), k i z * Real.exp (lam * D₁) := by
        refine sum_le_sum fun i hi => ?_
        have hz := (mem_filter.1 hi).2
        by_cases h0 : k i z = 0
        · rw [h0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hD₁ i z hz h0) hlam)) (hk0 i z hz)
    _ = (∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), k i z) * Real.exp (lam * D₁) := by
        rw [sum_mul]
    _ ≤ γ * Real.exp (lam * D₁) := mul_le_mul_of_nonneg_right (hcol z) (Real.exp_pos _).le

/-- **Monotonicity in the rate** (nonnegative coefficients, nonnegative distance). -/
theorem WeightedColumnW.mono {k : ι → ι → ℝ} (hk0 : ∀ i z, z ∉ ({i} : Finset ι) → 0 ≤ k i z)
    {dist : ι → ι → ℝ} (hd : ∀ x y, 0 ≤ dist x y) {lam lam' γ : ℝ} (hll : lam' ≤ lam)
    (h : WeightedColumnW k dist lam γ) : WeightedColumnW k dist lam' γ := by
  intro z
  refine le_trans (sum_le_sum fun i hi => ?_) (h z)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hll (hd z i)))
    (hk0 i z (mem_filter.1 hi).2)

/-- **W₁ influence coefficients are nonnegative** whenever the cost takes one positive value. -/
theorem siteInfluenceW_nonneg {supp : X → Finset ι} {V : X → (ι → S) → ℝ} {c : S → S → ℝ}
    (hc0 : ∀ a b, 0 ≤ c a b) {k : ι → ι → ℝ} (hk : SiteInfluenceW ν supp V c k) (hpos : ∃ a b, 0 < c a b) :
    ∀ i z, z ∉ ({i} : Finset ι) → 0 ≤ k i z := by
  intro i z hz
  obtain ⟨a, b, hab⟩ := hpos
  have h := hk i z hz (fun _ => a) b (fun _ => 0) 1 ⟨measurable_const, ⟨0, fun _ => by simp⟩⟩
    (fun _ _ _ => rfl) (fun ξ y t _ => by simpa using hc0 (ξ y) t)
  simp only [integral_zero, sub_self, abs_zero, mul_one] at h
  exact nonneg_of_mul_nonneg_left h hab

end Site

/-- The geodesic cost on SU(2) takes a positive value (`d(−1, 1) = π`). -/
theorem exists_geodSU2_pos : ∃ a b : SU2, 0 < geodSU2 a b := by
  refine ⟨negOneSU2, 1, ?_⟩
  have h : gaugeReTr SU2 2 (negOneSU2 * (1 : SU2)⁻¹) = -2 := by
    simp [gaugeReTr, gaugeTrace, negOneSU2, HasGaugeTrace.rep]
  unfold geodSU2
  rw [h]
  norm_num [Real.arccos_neg_one, Real.pi_pos]

/-! ## 3. D′ in W₁ form without a finite range -/

open ProofPhase.V3

/-- **D′ in W₁ form along the levels, weighted (named hypothesis, open; replaces `V3.LevelDprimeW`).** From some level
on, in every volume, the blocked law is the Gibbs measure of a bounded coarse potential (terms of arbitrary support,
`CoarsePot`) whose single-link W₁ influences (geodesic cost) have weighted column sums
`∑_{i ≠ z} k(i, z) e^{λ linkDist(z, i)} ≤ γ < 1`. No range clause. -/
def LevelDprimeWw (T : Tuning) (B : BlockingFamily T) (lam : ℝ) : Prop :=
  ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j, ∃ V : CoarsePot j,
    blockedLaw T B k j = Attempts.R3.gibbsMeasure (haarG SU2) V ∧ Attempts.R3.Potential (fun A => A) V ∧
    ∃ kk : LatticeLink 4 (coarseSide j) → LatticeLink 4 (coarseSide j) → ℝ,
      SiteInfluenceW (haarG SU2) (fun A => A) V geodSU2 kk ∧ WeightedColumnW kk linkDist lam γ

/-- **The weighted condition gives the W₁ block gap** (S): `LevelDprimeWw T B λ ⇒ BlockGapUnifW T B λ`, constant
`π/(1 − γ)`. -/
theorem blockGapUnifW_of_levelDprimeWw {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : LevelDprimeWw T B lam) : BlockGapUnifW T B lam := by
  obtain ⟨γ, hγ0, hγ1, k₀, H⟩ := h
  refine ⟨Real.pi / (1 - γ), div_nonneg Real.pi_pos.le (by linarith), k₀,
    fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ?_⟩
  obtain ⟨V, hgibbs, hpot, kk, hk', hcol⟩ := H k hk j
  have : Nonempty (LatticeLink 4 (coarseSide j)) := ⟨⟨fun _ => 0, 0⟩⟩
  rw [Effective.cov_map (T.ym k j) (B k j).meas hf hg]
  have e : (T.ym k j).map (B k j).B = Attempts.R3.gibbsMeasure (haarG SU2) V := hgibbs
  rw [e]
  exact decay_of_siteWw (haarG SU2) hpot geodSU2_nonneg geodSU2_le_pi hk' linkDist linkDist_self
    linkDist_triangle hlam hγ0 hγ1 hcol hf hg hfA hgS hvf hLg hvg hR

/-- **The old finite-range hypothesis is a special case** (S): `LevelDprimeW T B λ ⇒ LevelDprimeWw T B λ` for `λ ≥ 0`
(with `γ' = γ e^{λ D₁}`). -/
theorem levelDprimeWw_of_levelDprimeW {T : Tuning} {B : BlockingFamily T} {lam : ℝ} (hlam : 0 ≤ lam)
    (h : LevelDprimeW T B lam) : LevelDprimeWw T B lam := by
  obtain ⟨γ, D₁, hγ0, hρ, k₀, H⟩ := h
  refine ⟨γ * Real.exp (lam * D₁), mul_nonneg hγ0 (Real.exp_pos _).le, hρ, k₀, fun k hk j => ?_⟩
  obtain ⟨V, hgibbs, hpot, kk, hk', hcol, hD₁⟩ := H k hk j
  exact ⟨V, hgibbs, hpot, kk, hk',
    weightedColumn_le_of_range (siteInfluenceW_nonneg (haarG SU2) geodSU2_nonneg hk' exists_geodSU2_pos)
      linkDist hlam hcol hD₁⟩

/-- **Monotonicity in the rate** (S): `LevelDprimeWw T B λ ⇒ LevelDprimeWw T B λ'` for `λ' ≤ λ`. -/
theorem LevelDprimeWw.mono {T : Tuning} {B : BlockingFamily T} {lam lam' : ℝ} (hll : lam' ≤ lam)
    (h : LevelDprimeWw T B lam) : LevelDprimeWw T B lam' := by
  obtain ⟨γ, hγ0, hγ1, k₀, H⟩ := h
  refine ⟨γ, hγ0, hγ1, k₀, fun k hk j => ?_⟩
  obtain ⟨V, hgibbs, hpot, kk, hk', hcol⟩ := H k hk j
  exact ⟨V, hgibbs, hpot, kk, hk',
    hcol.mono (siteInfluenceW_nonneg (haarG SU2) geodSU2_nonneg hk' exists_geodSU2_pos) linkDist_nonneg hll⟩

/-- **The W₁ route with the weighted hypothesis** (S): `LevelDprimeWw` at a rate `λ > 0` and `ObsTransferPhysTW` give
the torus decay and the gap for bounded physical extent in both orders of limits. -/
theorem bothOrdersLoc_of_levelDprimeWw {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (B : BlockingFamily T) {lam : ℝ}
    (hlam : 0 < lam) (hD : LevelDprimeWw T B lam) (h3 : ObsTransferPhysTW T B) :
    ProofPhase.Torus.TorusDecayLoc T.toV ∧ MassGapLoc T ∧ ProofPhase.Torus.MassGapMFLoc T.toV := by
  have hT := torusDecayLoc_of_blockGapUnifW B hlam (blockGapUnifW_of_levelDprimeWw B hlam.le hD) h3
  exact ⟨hT, ProofPhase.Torus.bothOrdersLoc_of_torusDecayLoc ha hT⟩

end ProofPhase.Repair
