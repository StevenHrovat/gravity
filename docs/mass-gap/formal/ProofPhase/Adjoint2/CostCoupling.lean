/-
Proof phase, cycle 9, c9b round 2 (infrared): Dobrushin's comparison theorem in coupling form for a general site cost
(the W1 form), one smoothing step from the cost to the Hamming count, and the influence bound for test functions of
bounded per-site oscillation (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/ROUND2.md`, section 1.
-/

import ProofPhase.OneBox.CouplingDS
import ProofPhase.OneBox.Restricted
import ProofPhase.Adjoint2.Transfer

/-!
# The W1 form of the coupling theorem, and one smoothing step

`ProofPhase.OneBox.couplingDS_bound` (M1) counts disagreements: the influence hypothesis (I) and the conclusion are in
the Hamming cost `1[Y_x ≠ Y'_x]`. The certified condition at the cell scale (c4d) is in the **W1 form**: the conditional
law of one coarse link moves, in Kantorovich-Rubinstein distance, by at most `k · d(σ_z, σ'_z)` when a neighbour moves
(`d` the geodesic distance on SU(2)). This file does three things, generically (one site space `S`, finite sites `ι`):

* **Comparison theorem, any cost** (`costDS_bound`). A bounded measurable cost family `d x : S → S → ℝ` (zero on the
  diagonal), block couplings with (I) in cost form **with a source term** `a_b`
  (`Σ_{y ∈ B_b} v_y E_Q[d_y] ≤ a_b + Σ_{z ∉ B_b} K_bz v_z d_z(σ_z, σ'_z)`, in-support pairs only) and the column
  condition `Σ_{b ∌ z} K_bz ≤ γ c(z)`: for every `ε > 0` a coupling of `μ, μ'` with
  `Σ_x v_x E[d_x(Y_x, Y'_x)] ≤ Σ_b a_b/((1 - γ) c_min) + ε`. M1's `couplingDS_bound` is the case: Hamming cost
  (`hamming`), `a_b = 0` on good blocks, and on source blocks `K_b· = 0` with `a_b = Σ_{y ∈ B_b} v_y`, for which (I) holds
  for every pair (`influence_source_block`, any cost with bound `D`: `a_b = Σ_{y ∈ B_b} v_y D_y`). The source term is
  Dobrushin's comparison form (two specifications that differ near the changed boundary site).
* **One smoothing step** (`cost_bind_le`). A stationary coupling kernel (a `CouplingSpec` block, e.g. one heat-bath pass
  over a colour class of sites that share no interaction) whose output cost at in-support pairs is linear in the input
  cost: `Σ_x w_x E_Q[d'_x] ≤ a_0 + Σ_y Λ_y d_y(σ_y, σ'_y)`. Then the same holds after integrating over any supported
  coupling. Passes compose by applying it again (site-dependent cost families allow Hamming on the smoothed sites).
* **Test functions** (`abs_integral_sub_le_osc`): for `F` depending on `B` with per-site oscillation `≤ L`,
  `|∫ F dμ - ∫ F dμ'| ≤ L Σ_{x ∈ B} π(Y_x ≠ Y'_x)` for any coupling `π`. Together (`abs_integral_sub_le_costSmooth`,
  `isInfluenceBoundOn_of_costSmooth`): **W1 comparison + one smoothing step ⇒ the box influence of `FineOneBox`**, with
  `κ = a_0 + Λ̄ · Σ_b a_b/((1 - γ) c_min)` (`Λ_y ≤ Λ̄ v_y`).

Everything is generic; nothing here is about the Wilson measure. The instantiation (box laws of the blocked theory at
`L₁`, their single-link specifications, the W1 coefficients, the colour-class passes) is the note's section 1 (paper /
numerical for the fitted action, open for the true law).
-/

open MeasureTheory ProbabilityTheory Finset ProofPhase.OneBox ProofPhase.OneBox.CouplingSpec OneScale

open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Adjoint2

/-! ## 1. Site costs -/

/-- A bounded measurable cost on pairs of single-site values, zero on the diagonal. -/
structure SiteCost (S : Type*) [MeasurableSpace S] where
  c : S → S → ℝ
  meas : Measurable (fun q : S × S => c q.1 q.2)
  nonneg : ∀ a b, 0 ≤ c a b
  diag : ∀ a, c a a = 0
  D : ℝ
  le_D : ∀ a b, c a b ≤ D

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-- The cost at site `x` of a pair of configurations, for a site-dependent cost family. -/
def cst (d : ι → SiteCost S) (x : ι) (p : (ι → S) × (ι → S)) : ℝ := (d x).c (p.1 x) (p.2 x)

theorem measurable_cst (d : ι → SiteCost S) (x : ι) : Measurable (cst d x) := by
  have h : Measurable (fun p : (ι → S) × (ι → S) => (p.1 x, p.2 x)) :=
    ((measurable_pi_apply x).comp measurable_fst).prodMk ((measurable_pi_apply x).comp measurable_snd)
  exact (d x).meas.comp h

theorem cst_nonneg (d : ι → SiteCost S) (x : ι) (p : (ι → S) × (ι → S)) : 0 ≤ cst d x p := (d x).nonneg _ _

theorem abs_cst_le (d : ι → SiteCost S) (x : ι) (p : (ι → S) × (ι → S)) : |cst d x p| ≤ (d x).D := by
  rw [abs_of_nonneg (cst_nonneg d x p)]; exact (d x).le_D _ _

/-- The expected cost at site `x`. -/
def ecost (d : ι → SiteCost S) (x : ι) (π : Measure ((ι → S) × (ι → S))) : ℝ := ∫ p, cst d x p ∂π

theorem ecost_nonneg (d : ι → SiteCost S) (x : ι) (π : Measure ((ι → S) × (ι → S))) : 0 ≤ ecost d x π :=
  integral_nonneg fun p => cst_nonneg d x p

/-- The weighted expected cost `Σ_x v_x E_π[d_x(Y_x, Y'_x)]`. -/
def costPhi (d : ι → SiteCost S) (v : ι → ℝ) (π : Measure ((ι → S) × (ι → S))) : ℝ :=
  ∑ x, v x * ecost d x π

theorem costPhi_nonneg (d : ι → SiteCost S) {v : ι → ℝ} (hv : ∀ x, 0 ≤ v x) (π : Measure ((ι → S) × (ι → S))) :
    0 ≤ costPhi d v π :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hv x) (ecost_nonneg d x π)

/-- **The Hamming cost** `1[a ≠ b]`. -/
def hamming [MeasurableEq S] : SiteCost S where
  c a b := Set.indicator {q : S × S | q.1 ≠ q.2} (fun _ => (1 : ℝ)) (a, b)
  meas := by
    have h : MeasurableSet {q : S × S | q.1 ≠ q.2} := (measurableSet_eq_fun measurable_fst measurable_snd).compl
    exact (measurable_const.indicator h).comp (measurable_fst.prodMk measurable_snd)
  nonneg a b := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  diag a := Set.indicator_of_notMem (by simp) _
  D := 1
  le_D a b := by
    by_cases h : a = b
    · rw [Set.indicator_of_notMem (by simp [h])]; norm_num
    · rw [Set.indicator_of_mem (show (a, b) ∈ {q : S × S | q.1 ≠ q.2} from h)]

theorem cst_hamming [MeasurableEq S] (x : ι) (p : (ι → S) × (ι → S)) :
    cst (fun _ => (hamming : SiteCost S)) x p = (disagree x).indicator (fun _ => (1 : ℝ)) p := by
  show Set.indicator {q : S × S | q.1 ≠ q.2} (fun _ => (1 : ℝ)) (p.1 x, p.2 x) = _
  by_cases h : p.1 x = p.2 x
  · rw [Set.indicator_of_notMem (show p ∉ disagree x from fun hm => hm h),
      Set.indicator_of_notMem (show (p.1 x, p.2 x) ∉ {q : S × S | q.1 ≠ q.2} from fun hm => hm h)]
  · rw [Set.indicator_of_mem (show p ∈ disagree x from h),
      Set.indicator_of_mem (show (p.1 x, p.2 x) ∈ {q : S × S | q.1 ≠ q.2} from h)]

theorem ecost_hamming [MeasurableEq S] (x : ι) (π : Measure ((ι → S) × (ι → S))) :
    ecost (fun _ => (hamming : SiteCost S)) x π = π.real (disagree x) := by
  unfold ecost
  simp_rw [cst_hamming]
  exact integral_indicator_one (measurableSet_disagree x)

/-! ## 2. Integrating against one block update -/

section Bind

variable {β : Type*} [Fintype β] [DecidableEq β] {μ μ' : Measure (ι → S)} {C : CouplingSpec μ μ' β}

theorem integrable_cst (d : ι → SiteCost S) (x : ι) (π : Measure ((ι → S) × (ι → S))) [IsFiniteMeasure π] :
    Integrable (cst d x) π :=
  integrable_of_abs_le (measurable_cst d x) (abs_cst_le d x)

theorem ecost_bind [IsProbabilityMeasure μ] {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π) (b : β)
    (d : ι → SiteCost S) (x : ι) :
    ecost d x (π.bind (C.Q b)) = ∫ p, ecost d x (C.Q b p) ∂π := by
  have := h.isProbabilityMeasure
  exact integral_bind_eq π (C.Q b) (measurable_cst d x) (abs_cst_le d x)

theorem integrable_ecost_kernel [IsProbabilityMeasure μ] {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π)
    (b : β) (d : ι → SiteCost S) (x : ι) : Integrable (fun p => ecost d x (C.Q b p)) π := by
  have := h.isProbabilityMeasure
  exact integrable_integral_kernel π (C.Q b) (measurable_cst d x) (abs_cst_le d x)

/-- **Sites outside the block keep their cost.** -/
theorem ecost_bind_of_notMem [IsProbabilityMeasure μ] {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π)
    (b : β) (d : ι → SiteCost S) {x : ι} (hx : x ∉ C.B b) :
    ecost d x (π.bind (C.Q b)) = ecost d x π := by
  rw [ecost_bind h b d x]
  unfold ecost
  refine integral_congr_ae ?_
  filter_upwards [h.ae_mem] with p hp
  have h1 : ∀ᵐ w ∂(C.Q b p), w.1 x = p.1 x := by
    have := C.q_local b p.1 hp.1 x hx
    rw [← C.Q_fst' b hp] at this
    exact ae_of_ae_map measurable_fst.aemeasurable this
  have h2 : ∀ᵐ w ∂(C.Q b p), w.2 x = p.2 x := by
    have := C.q'_local b p.2 hp.2 x hx
    rw [← C.Q_snd' b hp] at this
    exact ae_of_ae_map measurable_snd.aemeasurable this
  have hc : ∀ᵐ w ∂(C.Q b p), cst d x w = cst d x p := by
    filter_upwards [h1, h2] with w hw1 hw2
    simp only [cst, hw1, hw2]
  rw [integral_congr_ae hc, integral_const]
  simp

/-- **One block, integrating the cost form of (I) over `π`.** -/
theorem block_cost_le [IsProbabilityMeasure μ] {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π)
    (d : ι → SiteCost S) {v : ι → ℝ} {a : β → ℝ} {K : β → ι → ℝ}
    (hI : ∀ b, ∀ σ ∈ C.Ω₀, ∀ σ' ∈ C.Ω₀',
      ∑ y ∈ C.B b, v y * ecost d y (C.Q b (σ, σ')) ≤ a b + ∑ z ∈ (C.B b)ᶜ, K b z * v z * cst d z (σ, σ'))
    (b : β) :
    ∑ y ∈ C.B b, v y * ecost d y (π.bind (C.Q b)) ≤ a b + ∑ z ∈ (C.B b)ᶜ, K b z * v z * ecost d z π := by
  have := h.isProbabilityMeasure
  have hL : ∑ y ∈ C.B b, v y * ecost d y (π.bind (C.Q b)) =
      ∫ p, ∑ y ∈ C.B b, v y * ecost d y (C.Q b p) ∂π := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [ecost_bind h b d y, integral_const_mul]
    · intro y _
      exact (integrable_ecost_kernel h b d y).const_mul _
  have hR : a b + ∑ z ∈ (C.B b)ᶜ, K b z * v z * ecost d z π =
      ∫ p, (a b + ∑ z ∈ (C.B b)ᶜ, K b z * v z * cst d z p) ∂π := by
    rw [integral_add (integrable_const _), integral_finsetSum, integral_const]
    · simp only [probReal_univ, one_smul]
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [ecost, integral_const_mul]
    · intro z _
      exact (integrable_cst d z π).const_mul _
    · exact integrable_finsetSum _ fun z _ => (integrable_cst d z π).const_mul _
  rw [hL, hR]
  refine integral_mono_ae ?_ ?_ ?_
  · exact integrable_finsetSum _ fun y _ => (integrable_ecost_kernel h b d y).const_mul _
  · exact (integrable_const _).add (integrable_finsetSum _ fun z _ => (integrable_cst d z π).const_mul _)
  · filter_upwards [h.ae_mem] with p hp
    exact hI b p.1 hp.1 p.2 hp.2

/-- **One smoothing step** (any block `b`, any input and output cost families). If at in-support pairs the block
coupling's output cost is linear in the input cost, the same holds after integrating over any supported coupling. -/
theorem cost_bind_le [IsProbabilityMeasure μ] {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π)
    (b : β) (d d' : ι → SiteCost S) {w Λ : ι → ℝ} {a₀ : ℝ}
    (hH : ∀ σ ∈ C.Ω₀, ∀ σ' ∈ C.Ω₀',
      ∑ x, w x * ecost d' x (C.Q b (σ, σ')) ≤ a₀ + ∑ y, Λ y * cst d y (σ, σ')) :
    ∑ x, w x * ecost d' x (π.bind (C.Q b)) ≤ a₀ + ∑ y, Λ y * ecost d y π := by
  have := h.isProbabilityMeasure
  have hL : ∑ x, w x * ecost d' x (π.bind (C.Q b)) = ∫ p, ∑ x, w x * ecost d' x (C.Q b p) ∂π := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [ecost_bind h b d' x, integral_const_mul]
    · intro x _
      exact (integrable_ecost_kernel h b d' x).const_mul _
  have hR : a₀ + ∑ y, Λ y * ecost d y π = ∫ p, (a₀ + ∑ y, Λ y * cst d y p) ∂π := by
    rw [integral_add (integrable_const _), integral_finsetSum, integral_const]
    · simp only [probReal_univ, one_smul]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [ecost, integral_const_mul]
    · intro y _
      exact (integrable_cst d y π).const_mul _
    · exact integrable_finsetSum _ fun y _ => (integrable_cst d y π).const_mul _
  rw [hL, hR]
  refine integral_mono_ae ?_ ?_ ?_
  · exact integrable_finsetSum _ fun x _ => (integrable_ecost_kernel h b d' x).const_mul _
  · exact (integrable_const _).add (integrable_finsetSum _ fun y _ => (integrable_cst d y π).const_mul _)
  · filter_upwards [h.ae_mem] with p hp
    exact hH p.1 hp.1 p.2 hp.2

end Bind

/-! ## 3. The averaged update contracts the weighted cost -/

section Contract

variable {β : Type*} [Fintype β] [DecidableEq β] {μ μ' : Measure (ι → S)} {C : CouplingSpec μ μ' β}

theorem ecost_T [IsProbabilityMeasure μ] [Nonempty β] {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π)
    (d : ι → SiteCost S) (x : ι) :
    ecost d x (C.T π) = (Fintype.card β : ℝ)⁻¹ * ∑ b, ecost d x (π.bind (C.Q b)) := by
  have hp : ∀ b, IsProbabilityMeasure (π.bind (C.Q b)) := fun b => (isSuppCoupling_bind h b).isProbabilityMeasure
  unfold ecost CouplingSpec.T
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [ENNReal.toReal_inv, smul_eq_mul]
  · intro b _
    exact integrable_cst d x _

/-- **One step, cost form:** `Φ_d(T π) ≤ θ Φ_d(π) + (Σ_b a_b)/N`, `θ = 1 - (1 - γ) c_min / N`. -/
theorem costPhi_T_le [IsProbabilityMeasure μ] [Nonempty β] {π : Measure ((ι → S) × (ι → S))}
    (h : C.IsSuppCoupling π) (d : ι → SiteCost S) {v : ι → ℝ} {a : β → ℝ} {K : β → ι → ℝ} {γ cmin : ℝ}
    (hv : ∀ x, 0 ≤ v x) (hγ : γ ≤ 1) (hc : ∀ x, cmin ≤ OneBox.coverage C.B x)
    (hI : ∀ b, ∀ σ ∈ C.Ω₀, ∀ σ' ∈ C.Ω₀',
      ∑ y ∈ C.B b, v y * ecost d y (C.Q b (σ, σ')) ≤ a b + ∑ z ∈ (C.B b)ᶜ, K b z * v z * cst d z (σ, σ'))
    (hK : ∀ z, ∑ b ∈ univ.filter (fun b => z ∉ C.B b), K b z ≤ γ * OneBox.coverage C.B z) :
    costPhi d v (C.T π) ≤ (1 - (1 - γ) * cmin / Fintype.card β) * costPhi d v π + (∑ b, a b) / Fintype.card β := by
  have hN : (0 : ℝ) < Fintype.card β := Nat.cast_pos.mpr Fintype.card_pos
  have he : ∀ x, 0 ≤ ecost d x π := fun x => ecost_nonneg d x π
  have hphiT : costPhi d v (C.T π) =
      (Fintype.card β : ℝ)⁻¹ * ∑ b, ∑ x, v x * ecost d x (π.bind (C.Q b)) := by
    calc costPhi d v (C.T π)
        = ∑ x, ∑ b, (Fintype.card β : ℝ)⁻¹ * (v x * ecost d x (π.bind (C.Q b))) := by
          simp only [costPhi, ecost_T h d, Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ b, ∑ x, (Fintype.card β : ℝ)⁻¹ * (v x * ecost d x (π.bind (C.Q b))) := Finset.sum_comm
      _ = _ := by simp only [Finset.mul_sum]
  have hsplit : ∀ b, ∑ x, v x * ecost d x (π.bind (C.Q b)) =
      ∑ x ∈ (C.B b)ᶜ, v x * ecost d x π + ∑ x ∈ C.B b, v x * ecost d x (π.bind (C.Q b)) := fun b => by
    rw [← Finset.sum_compl_add_sum (C.B b)]
    congr 1
    exact Finset.sum_congr rfl fun x hx => by rw [ecost_bind_of_notMem h b d (Finset.mem_compl.mp hx)]
  set O : β → ℝ := fun b => ∑ x ∈ (C.B b)ᶜ, v x * ecost d x π with hOdef
  have hOsum : ∑ b, O b = (Fintype.card β : ℝ) * costPhi d v π -
      ∑ x, (OneBox.coverage C.B x : ℝ) * (v x * ecost d x π) := by
    have : ∀ b, O b = costPhi d v π - ∑ x ∈ C.B b, v x * ecost d x π := fun b =>
      eq_sub_of_add_eq (Finset.sum_compl_add_sum (C.B b) _)
    rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_sub_distrib, OneBox.sum_blocks, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hKsum : ∑ b, ∑ z ∈ (C.B b)ᶜ, K b z * v z * ecost d z π ≤
      γ * ∑ x, (OneBox.coverage C.B x : ℝ) * (v x * ecost d x π) := by
    have e1 := OneBox.sum_good_compl C.B univ (fun b z => K b z * v z * ecost d z π)
    rw [e1, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    have : ∑ b ∈ univ.filter (fun b => z ∉ C.B b), K b z * v z * ecost d z π =
        (∑ b ∈ univ.filter (fun b => z ∉ C.B b), K b z) * (v z * ecost d z π) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, ← mul_assoc γ]
    exact mul_le_mul_of_nonneg_right (hK z) (mul_nonneg (hv z) (he z))
  have hcov : cmin * costPhi d v π ≤ ∑ x, (OneBox.coverage C.B x : ℝ) * (v x * ecost d x π) := by
    rw [costPhi, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hc x) (mul_nonneg (hv x) (he x))
  have htot : ∑ b, ∑ x, v x * ecost d x (π.bind (C.Q b)) ≤
      (Fintype.card β : ℝ) * costPhi d v π - (1 - γ) * cmin * costPhi d v π + ∑ b, a b := by
    have h1 : ∑ b, ∑ x, v x * ecost d x (π.bind (C.Q b)) ≤
        ∑ b, O b + (∑ b, a b + ∑ b, ∑ z ∈ (C.B b)ᶜ, K b z * v z * ecost d z π) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun b _ => ?_
      rw [hsplit b]
      have := block_cost_le h d hI b
      simp only [O]
      linarith
    have h4 : 0 ≤ 1 - γ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hcov h4]
  rw [hphiT]
  calc (Fintype.card β : ℝ)⁻¹ * ∑ b, ∑ x, v x * ecost d x (π.bind (C.Q b))
      ≤ (Fintype.card β : ℝ)⁻¹ *
          ((Fintype.card β : ℝ) * costPhi d v π - (1 - γ) * cmin * costPhi d v π + ∑ b, a b) :=
        mul_le_mul_of_nonneg_left htot (inv_nonneg.mpr hN.le)
    _ = _ := by field_simp

/-- **Source blocks satisfy (I) with `K = 0`**: for every block and every pair, the expected weighted cost on the block is at
most `Σ_{y ∈ B_b} v_y D_y`. So a block without an influence bound enters `CostWeights` with `a_b = Σ_{y ∈ B_b} v_y D_y`, `K_b· = 0`
(M1's source blocks, Hamming cost `D = 1`). -/
theorem influence_source_block (d : ι → SiteCost S) {v : ι → ℝ} (hv : ∀ x, 0 ≤ v x) (b : β) (σ σ' : ι → S) :
    ∑ y ∈ C.B b, v y * ecost d y (C.Q b (σ, σ')) ≤
      ∑ y ∈ C.B b, v y * (d y).D + ∑ z ∈ (C.B b)ᶜ, (0 : ℝ) * v z * cst d z (σ, σ') := by
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (hv y)
  have h := norm_integral_le_of_norm_le_const (μ := C.Q b (σ, σ')) (f := cst d y) (C := (d y).D)
    (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact abs_cst_le d y p)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
  exact (le_abs_self _).trans h

/-- **Admissible data, cost form**: weights `v ≥ 0`, source terms `a_b ≥ 0`, influence numbers `K`, `0 ≤ γ < 1`,
`c_min > 0` below the coverage, with (I) in cost form on every block (in-support pairs) and the column condition. -/
structure CostWeights (C : CouplingSpec μ μ' β) (d : ι → SiteCost S) where
  v : ι → ℝ
  a : β → ℝ
  K : β → ι → ℝ
  γ : ℝ
  cmin : ℝ
  v_nonneg : ∀ x, 0 ≤ v x
  a_nonneg : ∀ b, 0 ≤ a b
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1
  cmin_pos : 0 < cmin
  cmin_le : ∀ x, cmin ≤ OneBox.coverage C.B x
  influence : ∀ b, ∀ σ ∈ C.Ω₀, ∀ σ' ∈ C.Ω₀',
    ∑ y ∈ C.B b, v y * ecost d y (C.Q b (σ, σ')) ≤ a b + ∑ z ∈ (C.B b)ᶜ, K b z * v z * cst d z (σ, σ')
  column : ∀ z, ∑ b ∈ univ.filter (fun b => z ∉ C.B b), K b z ≤ γ * OneBox.coverage C.B z

namespace CostWeights

variable {d : ι → SiteCost S} (W : CostWeights C d)

/-- The bound `Σ_b a_b/((1 - γ) c_min)`. -/
def bound : ℝ := (∑ b, W.a b) / ((1 - W.γ) * W.cmin)

/-- The contraction rate `θ = 1 - (1 - γ) c_min / N`. -/
def θ : ℝ := 1 - (1 - W.γ) * W.cmin / Fintype.card β

theorem bound_nonneg : 0 ≤ W.bound :=
  div_nonneg (Finset.sum_nonneg fun b _ => W.a_nonneg b) (mul_nonneg (by linarith [W.γ_lt_one]) W.cmin_pos.le)

theorem θ_lt_one [Nonempty β] : W.θ < 1 := by
  have hN : (0 : ℝ) < Fintype.card β := Nat.cast_pos.mpr Fintype.card_pos
  have : 0 < (1 - W.γ) * W.cmin / Fintype.card β := div_pos (mul_pos (by linarith [W.γ_lt_one]) W.cmin_pos) hN
  simp only [θ]; linarith

theorem θ_nonneg [Nonempty ι] : 0 ≤ W.θ := by
  obtain ⟨x⟩ := ‹Nonempty ι›
  have h2 : (OneBox.coverage C.B x : ℝ) ≤ Fintype.card β := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_univ.le)
  have hN : (0 : ℝ) < Fintype.card β := by linarith [W.cmin_le x, W.cmin_pos]
  have hcN : W.cmin ≤ Fintype.card β := by linarith [W.cmin_le x]
  have : (1 - W.γ) * W.cmin / Fintype.card β ≤ 1 := by
    rw [div_le_one hN]; nlinarith [W.γ_nonneg, W.cmin_pos]
  simp only [θ]; linarith

theorem fixed_point [Nonempty β] : W.θ * W.bound + (∑ b, W.a b) / Fintype.card β = W.bound := by
  have hN : (Fintype.card β : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  have h1 : 1 - W.γ ≠ 0 := by linarith [W.γ_lt_one]
  have h2 : W.cmin ≠ 0 := W.cmin_pos.ne'
  simp only [θ, bound]
  field_simp
  ring

/-- **The bound along the explicit iterates** `π_n = T^n (μ ⊗ μ')`:
`Φ_d(π_n) ≤ Σ_b a_b/((1 - γ) c_min) + θ^n Φ_d(μ ⊗ μ')`. -/
theorem costPhi_iter_le [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Nonempty β] (n : ℕ) :
    costPhi d W.v (C.iter n) ≤ W.bound + W.θ ^ n * costPhi d W.v (μ.prod μ') := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : ∀ π : Measure ((ι → S) × (ι → S)), costPhi d W.v π = 0 := fun π => by
      simp [costPhi, Finset.univ_eq_empty]
    rw [h0, h0, mul_zero, add_zero]
    exact W.bound_nonneg
  induction n with
  | zero =>
      simp only [pow_zero, one_mul, CouplingSpec.iter, Function.iterate_zero, id]
      linarith [W.bound_nonneg]
  | succ n ih =>
      rw [iter_succ]
      have hstep := costPhi_T_le (isSuppCoupling_iter (C := C) n) d W.v_nonneg W.γ_lt_one.le W.cmin_le
        W.influence W.column
      have hθ := W.θ_nonneg
      have hfix := W.fixed_point
      simp only [θ] at hθ hfix ⊢
      calc costPhi d W.v (C.T (C.iter n))
          ≤ (1 - (1 - W.γ) * W.cmin / Fintype.card β) * costPhi d W.v (C.iter n) +
              (∑ b, W.a b) / Fintype.card β := hstep
        _ ≤ (1 - (1 - W.γ) * W.cmin / Fintype.card β) *
              (W.bound + (1 - (1 - W.γ) * W.cmin / Fintype.card β) ^ n * costPhi d W.v (μ.prod μ')) +
              (∑ b, W.a b) / Fintype.card β := by
            gcongr
            exact ih
        _ = _ := by rw [pow_succ]; linear_combination hfix

theorem eventually_costPhi_iter_le [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Nonempty β] {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ n in Filter.atTop, costPhi d W.v (C.iter n) ≤ W.bound + ε := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine Filter.Eventually.of_forall fun n => ?_
    have : costPhi d W.v (C.iter n) = 0 := by simp [costPhi, Finset.univ_eq_empty]
    rw [this]; linarith [W.bound_nonneg]
  have ht : Filter.Tendsto (fun n : ℕ => W.θ ^ n * costPhi d W.v (μ.prod μ')) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one W.θ_nonneg W.θ_lt_one).mul_const (costPhi d W.v (μ.prod μ'))
    simpa using this
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  linarith [W.costPhi_iter_le n]

end CostWeights

/-- **Dobrushin's comparison theorem in coupling form, any cost** (the W1 form with the geodesic cost). For every
`ε > 0` there is a coupling `π` of `μ, μ'` carried by `Ω₀ × Ω₀'` with `Σ_x v_x E_π[d_x] ≤ Σ_b a_b/((1 - γ) c_min) + ε`. -/
theorem costDS_bound [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Nonempty β] (C : CouplingSpec μ μ' β)
    {d : ι → SiteCost S} (W : CostWeights C d) {ε : ℝ} (hε : 0 < ε) :
    ∃ π : Measure ((ι → S) × (ι → S)), C.IsSuppCoupling π ∧ costPhi d W.v π ≤ W.bound + ε := by
  obtain ⟨n, hn⟩ := (W.eventually_costPhi_iter_le hε).exists
  exact ⟨C.iter n, isSuppCoupling_iter n, hn⟩

end Contract

/-! ## 4. Test functions of bounded per-site oscillation -/

section Osc

/-- **Telescoping.** A function of the sites in `B` with per-site oscillation `≤ L` changes by at most `L` times the
number of sites of `B` where the two configurations differ. -/
theorem abs_sub_le_card_disagree {B : Finset ι} {F : (ι → S) → ℝ} (hdep : DepOn F B) {L : ℝ}
    (hosc : ∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) (hL : 0 ≤ L) (σ σ' : ι → S) :
    |F σ - F σ'| ≤ L * ∑ x ∈ B, (disagree x).indicator (fun _ => (1 : ℝ)) (σ, σ') := by
  classical
  have key : ∀ s : Finset ι, ∀ τ : ι → S, (∀ x ∉ s, τ x = σ' x) →
      |F τ - F σ'| ≤ L * ((s.filter (fun x => x ∈ B ∧ τ x ≠ σ' x)).card : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro τ hτ
        have : τ = σ' := funext fun x => hτ x (Finset.notMem_empty x)
        subst this; simp
    | insert a s has ih =>
        intro τ hτ
        set τ' := Function.update τ a (σ' a)
        have hτ' : ∀ x ∉ s, τ' x = σ' x := by
          intro x hx
          by_cases hxa : x = a
          · subst hxa; simp [τ']
          · simp only [τ', Function.update_of_ne hxa]
            exact hτ x (by simp [hxa, hx])
        have h1 := ih τ' hτ'
        have hcard : (s.filter (fun x => x ∈ B ∧ τ' x ≠ σ' x)) = s.filter (fun x => x ∈ B ∧ τ x ≠ σ' x) := by
          refine Finset.filter_congr fun x hx => ?_
          have hxa : x ≠ a := fun e => has (e ▸ hx)
          simp [τ', Function.update_of_ne hxa]
        rw [hcard] at h1
        by_cases hab : a ∈ B ∧ τ a ≠ σ' a
        · have h2 : |F τ - F τ'| ≤ L := hosc τ a (σ' a) hab.1
          rw [Finset.filter_insert]
          rw [ite_eq_left hab, Finset.card_insert_of_notMem (fun hm => has (Finset.mem_filter.mp hm).1)]
          push_cast
          calc |F τ - F σ'| ≤ |F τ - F τ'| + |F τ' - F σ'| := abs_sub_le _ _ _
            _ ≤ L + L * ((s.filter (fun x => x ∈ B ∧ τ x ≠ σ' x)).card : ℝ) := add_le_add h2 h1
            _ = _ := by ring
        · rw [Finset.filter_insert]
          rw [ite_eq_right hab]
          have hF : F τ = F τ' := by
            refine hdep τ τ' fun x hx => ?_
            by_cases hxa : x = a
            · subst hxa
              simp only [τ', Function.update_self]
              by_contra hne
              exact hab ⟨hx, hne⟩
            · simp [τ', Function.update_of_ne hxa]
          rw [hF]; exact h1
  have h := key univ σ (fun x hx => absurd (Finset.mem_univ x) hx)
  refine h.trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) hL)
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun x => x ∈ B)]
  have h0 : ∑ x ∈ univ.filter (fun x => ¬ x ∈ B), (if x ∈ B ∧ σ x ≠ σ' x then ((1 : ℕ) : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun x hx => by simp [(Finset.mem_filter.mp hx).2]
  rw [h0, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_congr rfl fun x hx => ?_
  by_cases hne : σ x ≠ σ' x
  · rw [Set.indicator_of_mem (show (σ, σ') ∈ disagree x from hne)]; simp [hx, hne]
  · rw [Set.indicator_of_notMem (show (σ, σ') ∉ disagree x from hne)]; simp [hne]

/-- **Coupling bound for test functions of bounded per-site oscillation.** -/
theorem abs_integral_sub_le_osc [MeasurableEq S] {μ μ' : Measure (ι → S)} {π : Measure ((ι → S) × (ι → S))}
    [IsProbabilityMeasure π] (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = μ') {B : Finset ι}
    {F : (ι → S) → ℝ} (hF : BM F) (hdep : DepOn F B) {L : ℝ}
    (hosc : ∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) (hL : 0 ≤ L) :
    |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ L * ∑ x ∈ B, π.real (disagree x) := by
  obtain ⟨M, hM⟩ := hF.bdd
  have hint : ∀ g : (ι → S) × (ι → S) → ι → S, Measurable g → Integrable (fun p => F (g p)) π :=
    fun g hg => integrable_of_abs_le (hF.meas.comp hg) (fun p => hM _)
  rw [← hfst, ← hsnd, integral_map measurable_fst.aemeasurable hF.meas.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hF.meas.aestronglyMeasurable,
    ← integral_sub (hint _ measurable_fst) (hint _ measurable_snd)]
  have hI : Integrable (fun p => L * ∑ x ∈ B, (disagree x).indicator (fun _ => (1 : ℝ)) p) π :=
    (integrable_finsetSum _ fun x _ => (integrable_const _).indicator (measurableSet_disagree x)).const_mul _
  calc |∫ p, (F p.1 - F p.2) ∂π|
      ≤ ∫ p, |F p.1 - F p.2| ∂π := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := π) (fun p => F p.1 - F p.2)
    _ ≤ ∫ p, L * ∑ x ∈ B, (disagree x).indicator (fun _ => (1 : ℝ)) p ∂π :=
        integral_mono ((hint _ measurable_fst).sub (hint _ measurable_snd)).abs hI
          fun p => abs_sub_le_card_disagree hdep hosc hL p.1 p.2
    _ = L * ∑ x ∈ B, π.real (disagree x) := by
        rw [integral_const_mul, integral_finsetSum]
        · exact congrArg _ (Finset.sum_congr rfl fun x _ => integral_indicator_one (measurableSet_disagree x))
        · exact fun x _ => (integrable_const _).indicator (measurableSet_disagree x)

end Osc

/-! ## 5. W1 comparison plus one smoothing step gives the box influence -/

section Smooth

variable {β β' : Type*} [Fintype β] [DecidableEq β] [Fintype β'] [DecidableEq β']

/-- **The data of the W1-plus-smoothing route for one pair of box laws** `μ, μ'` (in the application: the box laws
under two boundary conditions differing at one outside cell). `C`: single-site (or small-block) heat-bath couplings with
the cost-form weights `W` (the W1 Dobrushin comparison, source terms near the changed cell); `Sm`, `b'`: the smoothing
kernel (one stationary coupling update `Sm.Q b'`; a sequence of colour-class passes must first be composed into one kernel,
and its bound `smooth` supplied: not done here), on the same supports, whose
Hamming output on the box `B₀` is `≤ a₀ + Σ_y Λ_y d_y` at in-support pairs, with `Λ_y ≤ Λ̄ v_y`. -/
structure CostSmoothData (μ μ' : Measure (ι → S)) (B₀ : Finset ι) (β β' : Type*) [Fintype β] [DecidableEq β]
    [Fintype β'] [DecidableEq β'] [MeasurableEq S] where
  C : CouplingSpec μ μ' β
  d : ι → SiteCost S
  W : CostWeights C d
  Sm : CouplingSpec μ μ' β'
  b' : β'
  supp : Sm.Ω₀ = C.Ω₀
  supp' : Sm.Ω₀' = C.Ω₀'
  Λ : ι → ℝ
  a₀ : ℝ
  Λbar : ℝ
  Λbar_nonneg : 0 ≤ Λbar
  Λ_le : ∀ y, Λ y ≤ Λbar * W.v y
  smooth : ∀ σ ∈ Sm.Ω₀, ∀ σ' ∈ Sm.Ω₀',
    ∑ x ∈ B₀, (Sm.Q b' (σ, σ')).real (disagree x) ≤ a₀ + ∑ y, Λ y * cst d y (σ, σ')

theorem sum_ind_mul (B₀ : Finset ι) (f : ι → ℝ) :
    ∑ x, (if x ∈ B₀ then (1 : ℝ) else 0) * f x = ∑ x ∈ B₀, f x := by
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- The influence constant of the data: `a₀ + Λ̄ Σ_b a_b/((1 - γ) c_min)`. -/
def CostSmoothData.kappa [MeasurableEq S] {μ μ' : Measure (ι → S)} {B₀ : Finset ι}
    (D : CostSmoothData μ μ' B₀ β β') : ℝ := D.a₀ + D.Λbar * D.W.bound

/-- **W1 comparison + one smoothing step ⇒ the influence bound** for test functions of the box with per-site
oscillation `≤ L`: `|∫ F dμ - ∫ F dμ'| ≤ L (a₀ + Λ̄ Σ_b a_b/((1 - γ) c_min))`. -/
theorem abs_integral_sub_le_costSmooth [MeasurableEq S] {μ μ' : Measure (ι → S)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [Nonempty β] {B₀ : Finset ι} (D : CostSmoothData μ μ' B₀ β β')
    {F : (ι → S) → ℝ} (hF : BM F) (hdep : DepOn F B₀) {L : ℝ}
    (hosc : ∀ ξ y t, y ∈ B₀ → |F ξ - F (Function.update ξ y t)| ≤ L) (hL : 0 ≤ L) :
    |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ L * D.kappa := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set c := L * D.Λbar
  have hc : 0 ≤ c := mul_nonneg hL D.Λbar_nonneg
  have hε : 0 < δ / (c + 1) := div_pos hδ (by linarith)
  obtain ⟨π, hπ, hΦ⟩ := costDS_bound D.C D.W hε
  have hπ' : D.Sm.IsSuppCoupling π := ⟨hπ.fst, hπ.snd, by rw [D.supp, D.supp']; exact hπ.supp⟩
  have hb := isSuppCoupling_bind hπ' D.b'
  have := hb.isProbabilityMeasure
  -- the smoothing step, Hamming output on `B₀`
  have hsm : ∑ x ∈ B₀, (π.bind (D.Sm.Q D.b')).real (disagree x) ≤ D.a₀ + ∑ y, D.Λ y * ecost D.d y π := by
    have e := cost_bind_le hπ' D.b' D.d (fun _ => (hamming : SiteCost S)) (w := fun x => if x ∈ B₀ then 1 else 0)
      (Λ := D.Λ) (a₀ := D.a₀) (fun σ hσ σ' hσ' => by
        have := D.smooth σ hσ σ' hσ'
        simp_rw [ecost_hamming]
        rw [sum_ind_mul]; exact this)
    simp_rw [ecost_hamming] at e
    rw [sum_ind_mul] at e
    exact e
  have hΛ : ∑ y, D.Λ y * ecost D.d y π ≤ D.Λbar * costPhi D.d D.W.v π := by
    rw [costPhi, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (D.Λ_le y) (ecost_nonneg _ _ _)
  have h1 := abs_integral_sub_le_osc hb.fst hb.snd hF hdep hosc hL
  have h2 : L * ∑ x ∈ B₀, (π.bind (D.Sm.Q D.b')).real (disagree x) ≤
      L * (D.a₀ + D.Λbar * (D.W.bound + δ / (c + 1))) := by
    refine mul_le_mul_of_nonneg_left (hsm.trans ?_) hL
    have := mul_le_mul_of_nonneg_left hΦ D.Λbar_nonneg
    linarith
  have h3 : c * (δ / (c + 1)) ≤ δ := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  calc |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ L * (D.a₀ + D.Λbar * (D.W.bound + δ / (c + 1))) := h1.trans h2
    _ = L * D.kappa + c * (δ / (c + 1)) := by simp only [CostSmoothData.kappa, c]; ring
    _ ≤ L * D.kappa + δ := by linarith

/-- **The box influence of `FineOneBox` from the W1-plus-smoothing data** (S). If for every boundary condition `σ` and
new value `s` at the outside site `z` the two box laws carry `CostSmoothData` with influence constant `≤ κ`, then `κ`
is an influence bound of `z` on the box, on every admissible class. -/
theorem isInfluenceBoundOn_of_costSmooth [MeasurableEq S] [Nonempty β] {Adm : (ι → S) → ((ι → S) → ℝ) → Prop}
    {B : Finset ι} (hB : B.Nonempty) {q : (ι → S) → Measure (ι → S)} [∀ σ, IsProbabilityMeasure (q σ)] {z : ι}
    {κ : ℝ} (h : ∀ σ s, ∃ D : CostSmoothData (q σ) (q (Function.update σ z s)) B β β', D.kappa ≤ κ) :
    IsInfluenceBoundOn Adm B q z κ := by
  intro σ s F L hF hdep _ hosc
  obtain ⟨D, hD⟩ := h σ s
  obtain ⟨y, hy⟩ := hB
  obtain ⟨ξ, -⟩ := nonempty_of_measure_ne_zero (μ := q σ) (s := Set.univ) (by simp)
  have hL : 0 ≤ L := (abs_nonneg _).trans (hosc ξ y (ξ y) hy)
  exact (abs_integral_sub_le_costSmooth D hF hdep hosc hL).trans
    ((mul_le_mul_of_nonneg_left hD hL).trans_eq (mul_comm _ _))

end Smooth

end ProofPhase.Adjoint2
