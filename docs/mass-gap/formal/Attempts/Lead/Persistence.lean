/-
Lead route attempt, the persistence lemma (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/lead/NOTE.md`, section 1.5 (Theorem D2).
-/

import OneScale.Decay

/-!
# The block Dobrushin comparison theorem (the engine of "further doublings keep it there")

Two probability measures `μ`, `μ'` on configurations, with block specifications `P`, `P'` over the **same** blocks.
`P` satisfies GDS with constant `γ < 1` and coverage at least `c₋ ≥ 1`. The two specifications differ by at most
`K_j · max_{y ∈ B_j} δ_y(h)` on block `j` (for every bounded measurable `h`). Then

  `|μ'(F) - μ(F)| ≤ (∑_j K_j) · L / (c₋ (1 - γ))`   for every `F` with all single-coordinate oscillations `≤ L`.

(`comparison`). This is Dobrushin's comparison theorem in Foellmer's dual form, block version; the proof is the
telescoping of Theorem A with `w ≡ 1`: `μ'(F) - μ'(P^t F) = ∑_{s<t} μ'(P' P^s F - P P^s F)` and `P^t F → μ(F)`.

**Use (NOTE §1.5, Theorem D2).** `μ = q_W^η`, `μ' = q_W^{η'}` are the measures of a box `W` with boundary conditions
differing at one frozen link `z`; the blocks are the side-`ℓ` cubes truncated to `W`; `K_j = k_{B_j}(z)` for the blocks
whose shell contains `z` and `0` otherwise. The conclusion is the influence bound
`k_W(z) ≤ (∑_{j : z ∈ ∂B_j} k_{B_j}(z)) / (c (1 - γ))` for the big box, in terms of the small boxes only: GDS at one
scale with `γ < 1` controls every larger box. The instantiation (block specifications of a box measure with frozen
boundary, i.e. the truncated-family DLR identity) is not formalised here; see the note.
-/

open MeasureTheory Finset Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.Lead

open OneScale

variable {ι S : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [MeasurableSpace S] {J : Type*} [Fintype J] [Nonempty J]

/-- `θ = 1 - c₋(1-γ)/M ≥ 0`, since `c₋ ≤ c(x) ≤ M`. -/
theorem theta_nonneg {μ : Measure (ι → S)} (P : BlockSpec μ J) {γ : ℝ} (hγ0 : 0 ≤ γ) {cmin : ℕ}
    (hcov : ∀ x, cmin ≤ coverage P.block x) :
    0 ≤ 1 - cmin * (1 - γ) / (Fintype.card J : ℝ) := by
  have hM0 : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  obtain ⟨x⟩ := (inferInstance : Nonempty ι)
  have hcM : (cmin : ℝ) ≤ Fintype.card J := by exact_mod_cast (hcov x).trans (P.coverage_le_card x)
  have hc0 : (0 : ℝ) ≤ cmin := Nat.cast_nonneg _
  have : (cmin : ℝ) * (1 - γ) ≤ Fintype.card J := by nlinarith
  rw [sub_nonneg, div_le_one hM0]
  exact this

/-- Oscillations of the iterates `P^t F` contract at rate `θ = 1 - c₋(1-γ)/M` (Step 1 with constant weight). -/
theorem osc_iter_const {μ : Measure (ι → S)} (P : BlockSpec μ J) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (k j z))
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hgds : GDS P.block k γ) {cmin : ℕ}
    (hcov : ∀ x, cmin ≤ coverage P.block x) (hc1 : 1 ≤ cmin)
    {F : (ι → S) → ℝ} (hF : BM F) {L : ℝ} (hL : 0 ≤ L) (hFL : OscBound F (fun _ => L)) :
    ∀ t : ℕ, OscBound (P.iter F t)
      (fun _ => (1 - cmin * (1 - γ) / (Fintype.card J : ℝ)) ^ t * L) := by
  set M : ℝ := (Fintype.card J : ℝ)
  set θ := 1 - cmin * (1 - γ) / M
  have hθ0 : 0 ≤ θ := theta_nonneg P hγ0 hcov
  intro t
  induction t with
  | zero => intro σ x s; rw [pow_zero, one_mul]; exact hFL σ x s
  | succ t ih =>
    rw [P.iter_succ]
    have hN : 0 ≤ θ ^ t * L := mul_nonneg (pow_nonneg hθ0 t) hL
    have hv : OscBound (P.iter F t) (fun x => θ ^ t * L * (fun _ : ι => (1 : ℝ)) x) := by
      simpa using ih
    have := P.oscBound_avg k hk hgds hcov hc1 (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one) zero_le_one
      (fun _ _ _ _ _ _ => by simp) (by linarith) hN (P.bm_iter hF t) hv
    refine this.mono fun x => le_of_eq ?_
    simp only [θ, M, mul_one, pow_succ]
    ring

/-- **The block comparison theorem.** -/
theorem comparison {μ μ' : Measure (ι → S)} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (P : BlockSpec μ J) (P' : BlockSpec μ' J) (hblock : ∀ j, P'.block j = P.block j)
    (k : J → ι → ℝ) (hk : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (k j z))
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hgds : GDS P.block k γ) {cmin : ℕ}
    (hcov : ∀ x, cmin ≤ coverage P.block x) (hc1 : 1 ≤ cmin)
    (K : J → ℝ) (hK0 : ∀ j, 0 ≤ K j)
    (hK : ∀ j (h : (ι → S) → ℝ) (m : ℝ), BM h → (∀ σ y t, y ∈ P.block j → |h σ - h (Function.update σ y t)| ≤ m) →
      ∀ σ, |blockAvg (P.block j) (P'.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ| ≤ K j * m)
    {F : (ι → S) → ℝ} (hF : BM F) {L : ℝ} (hL : 0 ≤ L) (hFL : OscBound F (fun _ => L)) :
    |∫ σ, F σ ∂μ' - ∫ σ, F σ ∂μ| ≤ (∑ j, K j) * L / (cmin * (1 - γ)) := by
  set M : ℝ := (Fintype.card J : ℝ)
  set θ := 1 - cmin * (1 - γ) / M
  have hM0 : 0 < M := by simp only [M]; exact_mod_cast Fintype.card_pos
  have hcpos : (0 : ℝ) < cmin := by exact_mod_cast hc1
  have hd : 0 < (cmin : ℝ) * (1 - γ) := mul_pos hcpos (by linarith)
  have h1θ : 1 - θ = cmin * (1 - γ) / M := by simp only [θ]; ring
  have hθ1 : θ < 1 := by have : 0 < cmin * (1 - γ) / M := div_pos hd hM0; linarith
  have hosc := osc_iter_const P k hk hγ0 hγ1.le hgds hcov hc1 hF hL hFL
  have hθ0 : 0 ≤ θ := theta_nonneg P hγ0 hcov
  set SK := ∑ j, K j
  have hSK : 0 ≤ SK := sum_nonneg fun j _ => hK0 j
  -- one step: `|μ'(h - P h)| ≤ M⁻¹ SK θ^s L` for `h = P^s F`
  have hstep : ∀ s, |∫ σ, (P.iter F s σ - P.iter F (s + 1) σ) ∂μ'| ≤ M⁻¹ * SK * (θ ^ s * L) := by
    intro s
    set h := P.iter F s
    have hh : BM h := P.bm_iter hF s
    have hPh := P.bm_avg' hh
    have hP'h := P'.bm_avg' hh
    have e1 : ∫ σ, (h σ - P.iter F (s + 1) σ) ∂μ' = ∫ σ, (P'.avg h σ - P.avg h σ) ∂μ' := by
      rw [P.iter_succ, integral_sub (hh.integrable μ') (hPh.integrable μ'),
        integral_sub (hP'h.integrable μ') (hPh.integrable μ'), P'.integral_avg hh]
    rw [e1]
    have hpt : ∀ σ, |P'.avg h σ - P.avg h σ| ≤ M⁻¹ * SK * (θ ^ s * L) := by
      intro σ
      have hdiff : P'.avg h σ - P.avg h σ =
          M⁻¹ * ∑ j, (blockAvg (P.block j) (P'.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ) := by
        unfold BlockSpec.avg
        simp_rw [hblock]
        rw [sum_sub_distrib]; ring
      rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 hM0), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hM0.le)
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [show SK * (θ ^ s * L) = ∑ j, K j * (θ ^ s * L) by rw [← sum_mul]]
      exact sum_le_sum fun j _ => hK j h _ hh (fun σ y t _ => hosc s σ y t) σ
    have := norm_integral_le_of_norm_le_const (μ := μ') (f := fun σ => P'.avg h σ - P.avg h σ)
      (C := M⁻¹ * SK * (θ ^ s * L)) (Eventually.of_forall fun σ => by rw [Real.norm_eq_abs]; exact hpt σ)
    simpa [Real.norm_eq_abs] using this
  -- telescoping under `μ'`
  have htel : ∀ t, ∫ σ, F σ ∂μ' =
      ∑ s ∈ range t, ∫ σ, (P.iter F s σ - P.iter F (s + 1) σ) ∂μ' + ∫ σ, P.iter F t σ ∂μ' := by
    intro t
    induction t with
    | zero => simp [BlockSpec.iter_zero]
    | succ t ih =>
      rw [ih, sum_range_succ, add_assoc,
        integral_sub ((P.bm_iter hF t).integrable μ') ((P.bm_iter hF (t + 1)).integrable μ')]
      ring
  -- the remainder
  have hrem : ∀ t, |∫ σ, P.iter F t σ ∂μ' - ∫ σ, F σ ∂μ| ≤ Fintype.card ι * (θ ^ t * L) := by
    intro t
    rw [← P.integral_iter hF t]
    set g := P.iter F t
    have hg : BM g := P.bm_iter hF t
    have e : ∫ σ, g σ ∂μ' - ∫ σ, g σ ∂μ = ∫ σ, (g σ - ∫ τ, g τ ∂μ) ∂μ' := by
      rw [integral_sub (hg.integrable μ') (integrable_const _)]; simp
    rw [e]
    have := norm_integral_le_of_norm_le_const (μ := μ') (f := fun σ => g σ - ∫ τ, g τ ∂μ)
      (C := ∑ _x : ι, θ ^ t * L) (Eventually.of_forall fun σ => by
        rw [Real.norm_eq_abs]; exact abs_sub_integral_le hg (hosc t) σ)
    simpa [Real.norm_eq_abs, sum_const, card_univ, nsmul_eq_mul] using this
  -- geometric sum
  have hgeom : ∀ t, ∑ s ∈ range t, θ ^ s ≤ M / (cmin * (1 - γ)) := by
    intro t
    have h1 := geom_sum_mul_neg θ t
    have hpos : 0 < 1 - θ := by linarith
    have : ∑ s ∈ range t, θ ^ s ≤ 1 / (1 - θ) := by
      rw [le_div_iff₀ hpos, h1]
      linarith [pow_nonneg hθ0 t]
    rw [h1θ] at this
    simpa [one_div_div] using this
  -- assemble, for every `t`
  have hall : ∀ t, |∫ σ, F σ ∂μ' - ∫ σ, F σ ∂μ| ≤
      SK * L / (cmin * (1 - γ)) + Fintype.card ι * (θ ^ t * L) := by
    intro t
    rw [htel t]
    have hsum : |∑ s ∈ range t, ∫ σ, (P.iter F s σ - P.iter F (s + 1) σ) ∂μ'| ≤ SK * L / (cmin * (1 - γ)) := by
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun s _ => hstep s).trans ?_)
      rw [show ∑ s ∈ range t, M⁻¹ * SK * (θ ^ s * L) = M⁻¹ * SK * L * ∑ s ∈ range t, θ ^ s by
        rw [Finset.mul_sum (range t) (fun s => θ ^ s) (M⁻¹ * SK * L)]
        exact Finset.sum_congr rfl fun s _ => by ring]
      calc M⁻¹ * SK * L * ∑ s ∈ range t, θ ^ s ≤ M⁻¹ * SK * L * (M / (cmin * (1 - γ))) :=
            mul_le_mul_of_nonneg_left (hgeom t) (mul_nonneg (mul_nonneg (inv_nonneg.2 hM0.le) hSK) hL)
        _ = SK * L / (cmin * (1 - γ)) := by field_simp
    calc |∑ s ∈ range t, ∫ σ, (P.iter F s σ - P.iter F (s + 1) σ) ∂μ' + ∫ σ, P.iter F t σ ∂μ' - ∫ σ, F σ ∂μ|
        ≤ |∑ s ∈ range t, ∫ σ, (P.iter F s σ - P.iter F (s + 1) σ) ∂μ'| +
            |∫ σ, P.iter F t σ ∂μ' - ∫ σ, F σ ∂μ| := by
          rw [add_sub_assoc]; exact abs_add_le _ _
      _ ≤ _ := add_le_add hsum (hrem t)
  -- let `t → ∞`
  have hlim : Tendsto (fun t : ℕ => SK * L / (cmin * (1 - γ)) + Fintype.card ι * (θ ^ t * L)) atTop
      (𝓝 (SK * L / (cmin * (1 - γ)) + Fintype.card ι * (0 * L))) :=
    tendsto_const_nhds.add (((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const L).const_mul _)
  simp only [zero_mul, mul_zero, add_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall hall)

end Attempts.Lead
