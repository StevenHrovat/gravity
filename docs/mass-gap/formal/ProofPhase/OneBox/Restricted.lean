/-
Proof phase, cycle 7, workstream 1 (c7c-onebox): Theorem A with influences tested only on an admissible class of
functions (the gauge-correct Dobrushin–Shlosman theorem, generic layer) (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c7c-onebox/NOTE.md`, section 3.
-/

import Attempts.R3.TailDecay

/-!
# Theorem A with restricted influences

`Attempts.R3.theoremA_w` asks the boundary influence `k_j(z)` to bound the change of `∫ F dq_j^σ` for **every** bounded
function `F` of the block with oscillation `≤ L` per site. For a gauge theory that is too much: a test function that is
not gauge invariant sees the gauge orientation of the block relative to its boundary, which is not physical. In the
proof of Theorem A the influence bound is only ever applied to the functions `ξ ↦ h(σ_{Ω∖B}, ξ_B)` with `h` an iterate
of the test function `g` under the averaged block operator. So it is enough to know the influence on an **admissible
class** that contains these functions:

* `IsInfluenceBoundOn Adm B q z k`: the influence bound, tested only on `F` with `Adm σ' F` at the moved boundary `σ'`.
* `theoremA_on`: Theorem A (weighted form, as `theoremA_w`) for `g` in an invariant class `Inv` which is closed under
  the averaged block operator, provided `Inv h` makes `ξ ↦ h(σ_{Ω∖B_j}, ξ)` admissible for the block `j` at `σ`.

The proofs follow `OneScale.osc_blockAvg_of_not_mem`, `Attempts.R3.oscBound_avg_w` and `theoremA_w` line by line; only
the admissibility bookkeeping is added. With `Adm = True` this is `theoremA_w` (`isInfluenceBoundOn_of`).
-/

open MeasureTheory Finset OneScale

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OneBox

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-- **Influence bound on an admissible class.** `k` bounds the influence of the outside coordinate `z` on the block
specification `q` of `B`, tested on bounded measurable functions of the block that are admissible at the moved
boundary condition. -/
def IsInfluenceBoundOn (Adm : (ι → S) → ((ι → S) → ℝ) → Prop) (B : Finset ι) (q : (ι → S) → Measure (ι → S))
    (z : ι) (k : ℝ) : Prop :=
  ∀ (σ : ι → S) (s : S) (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B → Adm (Function.update σ z s) F →
    (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) →
    |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q (Function.update σ z s))| ≤ k * L

/-- The unrestricted influence bound is an influence bound on every class. -/
theorem isInfluenceBoundOn_of {Adm : (ι → S) → ((ι → S) → ℝ) → Prop} {B : Finset ι}
    {q : (ι → S) → Measure (ι → S)} {z : ι} {k : ℝ} (h : IsInfluenceBound B q z k) :
    IsInfluenceBoundOn Adm B q z k :=
  fun σ s F L hF hdep _ hosc => h σ s F L hF hdep hosc

/-- **Lemma 2.5 (H) on an admissible class.** As `OneScale.osc_blockAvg_of_not_mem`, with the influence bound only
on the admissible class, which must contain the boundary-frozen restriction of `h`. -/
theorem osc_blockAvg_of_not_mem_on {Adm : (ι → S) → ((ι → S) → ℝ) → Prop} {B : Finset ι}
    {q : (ι → S) → Measure (ι → S)} [∀ σ, IsProbabilityMeasure (q σ)] {x : ι} (hx : x ∉ B) {k : ℝ}
    (hk : IsInfluenceBoundOn Adm B q x k)
    {h : (ι → S) → ℝ} (hh : BM h) {v : ι → ℝ} (hv : OscBound h v) {m : ℝ} (hm : ∀ y ∈ B, v y ≤ m)
    (σ : ι → S) (s : S) (hadm : Adm (Function.update σ x s) (fun ξ => h (splice B (Function.update σ x s) ξ))) :
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
  have h2 := hk σ s F m hF hFdep hadm hFosc
  have hsplit : blockAvg B q h σ - blockAvg B q h σ' =
      ∫ ξ, (h (splice B σ ξ) - F ξ) ∂(q σ) + (∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q σ')) := by
    unfold blockAvg
    rw [integral_sub (integrable_comp_splice hh σ _) (hF.integrable _)]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

variable {J : Type*} [Fintype J] {μ : Measure (ι → S)} (P : BlockSpec μ J)

/-- **The admissibility data.** An invariant class `Inv` of test functions, closed under the averaged block operator,
whose members restrict (boundary frozen) to admissible functions of every block. -/
structure AdmData (Adm : J → (ι → S) → ((ι → S) → ℝ) → Prop) (Inv : ((ι → S) → ℝ) → Prop) : Prop where
  avg : ∀ h, BM h → Inv h → Inv (P.avg h)
  restrict : ∀ j h σ, Inv h → Adm j σ (fun ξ => h (splice (P.block j) σ ξ))

/-- **Step 1 under the weighted condition, admissible class.** As `Attempts.R3.oscBound_avg_w`. -/
theorem oscBound_avg_on {Adm : J → (ι → S) → ((ι → S) → ℝ) → Prop} {Inv : ((ι → S) → ℝ) → Prop}
    (hA : AdmData P Adm Inv) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundOn (Adm j) (P.block j) (P.spec j) z (k j z))
    (e : J → ι → ℝ) {γ : ℝ} (hgds : Attempts.R3.GDSw P.block k e γ) {cmin : ℕ}
    (hcov : ∀ x, cmin ≤ coverage P.block x)
    (hc1 : 1 ≤ cmin) {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → w y ≤ e j x * w x) (hγ1 : γ ≤ 1)
    {Nn : ℝ} (hN : 0 ≤ Nn) {h : (ι → S) → ℝ} (hh : BM h) (hInv : Inv h) (hv : OscBound h (fun x => Nn * w x)) :
    OscBound (P.avg h) (fun x => (1 - cmin * (1 - γ) / Fintype.card J) * (Nn * w x)) := by
  intro σ x s
  set σ' := Function.update σ x s
  set M : ℝ := (Fintype.card J : ℝ)
  have hM : (1 : ℝ) ≤ M := by
    have := (hc1.trans (hcov x)).trans (P.coverage_le_card x)
    simp only [M]
    exact_mod_cast this
  have hM0 : 0 < M := by linarith
  set t : J → ℝ := fun j =>
    |blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ'|
  have ht_in : ∀ j, x ∈ P.block j → t j = 0 := by
    intro j hj
    simp only [t, σ', blockAvg_update_mem (P.spec_congr j) h hj σ s, sub_self, abs_zero]
  have ht_out : ∀ j, x ∉ P.block j → t j ≤ Nn * w x + k j x * (Nn * (e j x * w x)) := by
    intro j hj
    have hm : ∀ y ∈ P.block j, Nn * w y ≤ Nn * (e j x * w x) := fun y hy =>
      mul_le_mul_of_nonneg_left (hwk j x y hj hy) hN
    have := P.isProb j
    exact osc_blockAvg_of_not_mem_on hj (hk j x hj) hh hv hm σ s (hA.restrict j h σ' hInv)
  have hNw : 0 ≤ Nn * w x := mul_nonneg hN (hw0 x)
  have hsum : ∑ j, t j ≤ (M - coverage P.block x) * (Nn * w x) + Nn * w x * (γ * coverage P.block x) := by
    rw [← sum_filter_add_sum_filter_not univ (fun j => x ∈ P.block j)]
    rw [sum_eq_zero (fun j hj => ht_in j (mem_filter.1 hj).2), zero_add]
    calc ∑ j ∈ univ.filter (fun j => x ∉ P.block j), t j
        ≤ ∑ j ∈ univ.filter (fun j => x ∉ P.block j), (Nn * w x + k j x * (Nn * (e j x * w x))) :=
          sum_le_sum fun j hj => ht_out j (mem_filter.1 hj).2
      _ = (M - coverage P.block x) * (Nn * w x) +
          Nn * w x * ∑ j ∈ univ.filter (fun j => x ∉ P.block j), k j x * e j x := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, P.card_not_mem x, mul_sum]
          congr 1
          refine sum_congr rfl fun j _ => ?_
          ring
      _ ≤ _ := by
          gcongr
          exact hgds x
  have hdiff : P.avg h σ - P.avg h σ' =
      M⁻¹ * ∑ j, (blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ') := by
    unfold BlockSpec.avg; rw [sum_sub_distrib]; ring
  have hcx : (cmin : ℝ) ≤ coverage P.block x := by exact_mod_cast hcov x
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 hM0)]
  calc M⁻¹ * |∑ j, (blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ')|
      ≤ M⁻¹ * ∑ j, t j := mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (inv_nonneg.2 hM0.le)
    _ ≤ M⁻¹ * ((M - coverage P.block x) * (Nn * w x) + Nn * w x * (γ * coverage P.block x)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hM0.le)
    _ = M⁻¹ * ((M - coverage P.block x * (1 - γ)) * (Nn * w x)) := by ring
    _ ≤ M⁻¹ * ((M - cmin * (1 - γ)) * (Nn * w x)) := by
        gcongr
    _ = (1 - cmin * (1 - γ) / M) * (Nn * w x) := by
        field_simp

/-- **The core estimate, admissible class.** As `Attempts.R3.cov_le_weighted_w`, for `g` in the invariant class. -/
theorem cov_le_weighted_on [IsProbabilityMeasure μ] [Nonempty ι] {Adm : J → (ι → S) → ((ι → S) → ℝ) → Prop}
    {Inv : ((ι → S) → ℝ) → Prop} (hA : AdmData P Adm Inv) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundOn (Adm j) (P.block j) (P.spec j) z (k j z))
    (e : J → ι → ℝ) {γ : ℝ} (hγ : 0 ≤ γ) (hgds : Attempts.R3.GDSw P.block k e γ) {cmin : ℕ} (hc1 : 1 ≤ cmin)
    (hcov : ∀ x, cmin ≤ coverage P.block x) {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → w y ≤ e j x * w x) (hρ : γ < 1)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) (hgI : Inv g) {A : Finset ι} (hfA : DepOn f A) {vf : ι → ℝ}
    (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun x => Lg * w x)) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      Lg / (cmin * (1 - γ)) * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty ι)
  set M : ℝ := (Fintype.card J : ℝ)
  have hMc : cmin ≤ Fintype.card J := (hcov x₀).trans (P.coverage_le_card x₀)
  have hJ : Nonempty J := Fintype.card_pos_iff.1 (by omega)
  have hM0 : 0 < M := by simp only [M]; exact_mod_cast (by omega : 0 < Fintype.card J)
  have hcm : (1 : ℝ) ≤ cmin := by exact_mod_cast hc1
  have hcM : (cmin : ℝ) ≤ M := by simp only [M]; exact_mod_cast hMc
  have hgap : 0 < 1 - γ := by linarith
  set θ : ℝ := 1 - cmin * (1 - γ) / M with hθ
  have hθ1 : θ < 1 := by
    have : 0 < cmin * (1 - γ) / M := div_pos (mul_pos (by linarith) hgap) hM0
    linarith
  have hθ0 : 0 ≤ θ := by
    have : cmin * (1 - γ) / M ≤ 1 := by
      rw [div_le_one hM0]
      nlinarith
    linarith
  have hInvIter : ∀ t, Inv (P.iter g t) := by
    intro t
    induction t with
    | zero => simpa [BlockSpec.iter_zero] using hgI
    | succ t ih => rw [BlockSpec.iter_succ]; exact hA.avg _ (P.bm_iter hg t) ih
  have hosc : ∀ t, OscBound (P.iter g t) (fun x => θ ^ t * Lg * w x) := by
    intro t
    induction t with
    | zero => simpa [BlockSpec.iter_zero] using hvg
    | succ t ih =>
      rw [BlockSpec.iter_succ]
      have h := oscBound_avg_on P hA k hk e hgds hcov hc1 hw0 hwk hρ.le (Nn := θ ^ t * Lg)
        (mul_nonneg (pow_nonneg hθ0 t) hLg) (P.bm_iter hg t) (hInvIter t) (by simpa [mul_assoc] using ih)
      refine h.mono fun x => le_of_eq ?_
      rw [pow_succ]; ring
  have hD0 : 0 < (cmin : ℝ) * (1 - γ) := mul_pos (by linarith) hgap
  exact P.cov_le_of_iter_osc hθ0 hθ1 hD0 (by simp only [θ, M]; field_simp; ring) hw0 hf hg hfA hvf hLg hosc

/-- **Theorem A with restricted influences** (weighted, no finite range). As `Attempts.R3.theoremA_w`, with the
influence bounds only on the admissible classes and `g` in the invariant class:
`|μ(f g) − μ(f) μ(g)| ≤ b/(c₋(1 − γ)) · (c₊ ∑_{a ∈ A} v_a) · L_g · e^{−λ(R − D₀)}`. -/
theorem theoremA_on [IsProbabilityMeasure μ] [Nonempty ι] {Adm : J → (ι → S) → ((ι → S) → ℝ) → Prop}
    {Inv : ((ι → S) → ℝ) → Prop} (hA : AdmData P Adm Inv) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundOn (Adm j) (P.block j) (P.spec j) z (k j z))
    {cmin cmax b : ℕ} (hc1 : 1 ≤ cmin)
    (hcov : ∀ x, cmin ≤ coverage P.block x) (hcmax : ∀ x, coverage P.block x ≤ cmax)
    (hb : ∀ j, (P.block j).card ≤ b)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {D₀ : ℝ} (hD₀ : ∀ j, ∀ x ∈ P.block j, ∀ y ∈ P.block j, dist x y ≤ D₀)
    (E : J → ι → ℝ) (hE : ∀ j x y, x ∉ P.block j → y ∈ P.block j → dist x y ≤ E j x)
    {lam : ℝ} (hlam : 0 ≤ lam) {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hgds : Attempts.R3.GDSw P.block k (fun j x => Real.exp (lam * E j x)) γ)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) (hgI : Inv g) {A Sg : Finset ι} (hfA : DepOn f A)
    (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      b / (cmin * (1 - γ)) * (cmax * ∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * (R - D₀))) := by
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure μ
  set w := expWeight dist lam Sg
  set e := Real.exp (-(lam * (R - D₀)))
  have hw0 : ∀ x, 0 ≤ w x := expWeight_nonneg dist lam Sg
  have hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → w y ≤ Real.exp (lam * E j x) * w x := by
    intro j x y hx hy
    refine (expWeight_le_mul dist htri hlam Sg x y).trans (mul_le_mul_of_nonneg_right ?_ (hw0 x))
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hE j x y hx hy) hlam)
  have hvg' : OscBound g (fun x => Lg * w x) := by
    intro σ x s
    by_cases hx : x ∈ Sg
    · calc |g σ - g (Function.update σ x s)| ≤ Lg := hvg σ x s
        _ = Lg * 1 := (mul_one _).symm
        _ ≤ Lg * w x := mul_le_mul_of_nonneg_left (one_le_expWeight dist hd0 lam hx) hLg
    · rw [hgS.update_eq hx σ s, sub_self, abs_zero]
      exact mul_nonneg hLg (hw0 x)
  have hcore := cov_le_weighted_on P hA k hk (fun j x => Real.exp (lam * E j x)) hγ hgds hc1 hcov hw0 hwk hγ1
    hf hg hgI hfA hvf hLg hvg'
  refine hcore.trans ?_
  have hvf0 : ∀ a, 0 ≤ vf a := fun a => hvf.nonneg σ₀ a
  have hgap : 0 < 1 - γ := by linarith
  have hpre : 0 ≤ Lg / (cmin * (1 - γ)) :=
    div_nonneg hLg (mul_nonneg (Nat.cast_nonneg _) hgap.le)
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
  calc Lg / (cmin * (1 - γ)) * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y
      ≤ Lg / (cmin * (1 - γ)) * ((cmax * ∑ a ∈ A, vf a) * (b * e)) := mul_le_mul_of_nonneg_left hsum hpre
    _ = b / (cmin * (1 - γ)) * (cmax * ∑ a ∈ A, vf a) * Lg * e := by ring

end ProofPhase.OneBox
