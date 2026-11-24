/-
P vs NP dictionary, Lean part 1: a Dobrushin influence sum below 1 gives fast mixing of single-site dynamics
(2026-11-23). Released under Apache 2.0.

Paper: `docs/pnp/DICTIONARY.md`, section 2.
-/

import ProofPhase.OneBox.CouplingDS

/-!
# Influence below 1 gives fast mixing

**Setting.** A finite site set `ι` with `n = card ι` sites, one measurable single-site space `S` with a measurable
diagonal, configurations `ι → S`, a probability measure `μ` on configurations (the equilibrium, e.g. a Gibbs measure).

* `SiteDynamics μ`: single-site update kernels `P x` (the heat-bath or Gibbs-sampler update at `x` is the example; any
  update with the listed properties will do) that change only the spin at `x` and leave `μ` invariant, together with
  measurable coupling kernels `Q x` of `P x σ` and `P x σ'` and an influence matrix `A x z ≥ 0` (the influence of the
  site `z` on the site `x`) such that the coupled update at `x` disagrees at `x` with probability at most
  `Σ_z A x z [σ z ≠ σ' z]`. This is the coupling form of Dobrushin's condition: for the heat-bath update, `A x z` is
  Dobrushin's coefficient (the largest total-variation distance between the conditional laws at `x` given two
  boundary conditions that differ only at `z`) and `Q x` glues maximal couplings along a chain of hybrid boundary
  conditions. That construction is classical and, as M1's hypothesis (C), is **assumed** here, not proved.
* Systematic scan: one sweep updates the sites in a list `order` that contains every site (`sweep`).
* Random scan: one step picks a site uniformly and updates it (`rsStep`), the averaged update of M1's `T`.

**Main results.**
* `tv_sweep_le`: **systematic scan, row sums.** If `Σ_z A x z ≤ α` for every `x` (Dobrushin's original condition) with
  `α < 1`, then for every start `ν` and every measurable set `s`, `|ν_t(s) - μ(s)| ≤ n α^t` after `t` sweeps.
* `tv_rs_le`: **random scan, column sums.** If `Σ_x A x z ≤ α` for every `z` (the column condition of M1's
  `couplingDS_bound`, with one-site blocks) with `α < 1`, then after `k` single-site steps
  `|ν_k(s) - μ(s)| ≤ n (1 - (1 - α)/n)^k ≤ n e^{-(1 - α) k / n}`.
* `mixing_sweep`, `mixing_rs`: **mixing times.** Distance at most `ε` after `t ≥ log(n/ε)/log(1/α)` sweeps, that is
  `O(log n)` sweeps of `n` updates each, and after `k ≥ n log(n/ε)/(1 - α)` random single-site updates: both
  `O(n log n)` single-site updates for fixed `α < 1` and `ε`.
* `integral_sweep_le`, `integral_rs_le`: the same for bounded test functions, `|∫ F dν_t - ∫ F dμ| ≤ 2 M n α^t`, through
  M1's `abs_integral_sub_le_phi`.

**Reused from M1** (`ProofPhase.OneBox.CouplingDS`): the disagreement events `disagree`, their measurability, the
functional `phi`, and the passage from a coupling to test functions `abs_integral_sub_le_phi`. M1's theorem compares
two *invariant* measures (its couplings keep both marginals fixed); **new here** is the dynamics from an arbitrary
start: the coupled chain whose first marginal is the law of the sampler at time `t` and whose second marginal stays
`μ`, the per-site estimates without support hypotheses, the max-norm (Gauss-Seidel) contraction of a whole sweep, the
total-variation bounds, and the mixing times.

**Simplifying choices (stated, none hidden).** The kernel hypotheses are asked for every configuration (no supports):
this covers models with soft constraints (all of lattice gauge theory and spin systems with positive weights); hard
constraints (proper colourings) would need M1's support sets. The scan list may repeat sites; it must contain every
site.
-/

open MeasureTheory ProbabilityTheory Finset ProofPhase.OneBox

open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Mixing

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-- Pairs of configurations. -/
abbrev Pair (ι S : Type*) := (ι → S) × (ι → S)

/-! ### Generic facts on binding a probability measure with a Markov kernel -/

section Generic

variable {α : Type*} [MeasurableSpace α]

theorem isProbabilityMeasure_bind {π : Measure α} [IsProbabilityMeasure π] (κ : Kernel α α) [IsMarkovKernel κ] :
    IsProbabilityMeasure (π.bind κ) :=
  ⟨by rw [Measure.bind_apply MeasurableSet.univ κ.aemeasurable]; simp⟩

theorem bind_real {π : Measure α} [IsProbabilityMeasure π] (κ : Kernel α α) [IsMarkovKernel κ]
    {s : Set α} (hs : MeasurableSet s) : (π.bind κ).real s = ∫ p, (κ p).real s ∂π := by
  rw [measureReal_def, Measure.bind_apply hs κ.aemeasurable]
  rw [← integral_toReal ((Kernel.measurable_coe _ hs).aemeasurable) (ae_of_all _ fun p => measure_lt_top _ _)]
  rfl

theorem integrable_kernel_real {π : Measure α} [IsProbabilityMeasure π] (κ : Kernel α α) [IsMarkovKernel κ]
    {s : Set α} (hs : MeasurableSet s) : Integrable (fun p => (κ p).real s) π := by
  refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun p => ?_)
  · exact (Kernel.measurable_coe _ hs).ennreal_toReal.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

end Generic

/-! ### The data -/

/-- **Single-site dynamics with a Dobrushin influence matrix** (coupling form). -/
structure SiteDynamics (μ : Measure (ι → S)) where
  /-- The single-site update at `x` (heat-bath: resample the spin at `x` from its conditional law). -/
  P : ι → Kernel (ι → S) (ι → S)
  P_markov : ∀ x, IsMarkovKernel (P x)
  /-- The update at `x` changes only the spin at `x`. -/
  P_local : ∀ x σ, ∀ z, z ≠ x → ∀ᵐ ξ ∂(P x σ), ξ z = σ z
  /-- The update at `x` leaves `μ` invariant (for the heat-bath update this is the DLR equation at `x`). -/
  P_inv : ∀ x, μ.bind (P x) = μ
  /-- Measurable couplings of the updates from two configurations. -/
  Q : ι → Kernel (Pair ι S) (Pair ι S)
  Q_markov : ∀ x, IsMarkovKernel (Q x)
  Q_fst : ∀ x (p : Pair ι S), (Q x p).map Prod.fst = P x p.1
  Q_snd : ∀ x (p : Pair ι S), (Q x p).map Prod.snd = P x p.2
  /-- The influence matrix: `A x z` is the influence of the site `z` on the site `x`. -/
  A : ι → ι → ℝ
  A_nonneg : ∀ x z, 0 ≤ A x z
  /-- **Dobrushin's condition in coupling form.** -/
  influence : ∀ x (p : Pair ι S), (Q x p).real (disagree x) ≤ ∑ z, (disagree z).indicator (fun _ => A x z) p

namespace SiteDynamics

variable {μ : Measure (ι → S)} (D : SiteDynamics μ)

instance (x : ι) : IsMarkovKernel (D.P x) := D.P_markov x
instance (x : ι) : IsMarkovKernel (D.Q x) := D.Q_markov x

/-! ### One coupled update -/

theorem bind_map_fst (π : Measure (Pair ι S)) (x : ι) :
    (π.bind (D.Q x)).map Prod.fst = (π.map Prod.fst).bind (D.P x) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, Measure.bind_apply (measurable_fst hs) (D.Q x).aemeasurable,
    Measure.bind_apply hs (D.P x).aemeasurable, lintegral_map (Kernel.measurable_coe _ hs) measurable_fst]
  refine lintegral_congr fun p => ?_
  rw [← Measure.map_apply measurable_fst hs, D.Q_fst]

theorem bind_map_snd (π : Measure (Pair ι S)) (x : ι) :
    (π.bind (D.Q x)).map Prod.snd = (π.map Prod.snd).bind (D.P x) := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs, Measure.bind_apply (measurable_snd hs) (D.Q x).aemeasurable,
    Measure.bind_apply hs (D.P x).aemeasurable, lintegral_map (Kernel.measurable_coe _ hs) measurable_snd]
  refine lintegral_congr fun p => ?_
  rw [← Measure.map_apply measurable_snd hs, D.Q_snd]

variable [MeasurableEq S]

/-- **Off the updated site the pair is kept.** -/
theorem bind_disagree_le_of_ne {π : Measure (Pair ι S)} [IsProbabilityMeasure π] {x z : ι} (hzx : z ≠ x) :
    (π.bind (D.Q x)).real (disagree z) ≤ π.real (disagree z) := by
  rw [bind_real _ (measurableSet_disagree z), ← integral_indicator_one (measurableSet_disagree z)]
  refine integral_mono (integrable_kernel_real _ (measurableSet_disagree z))
    ((integrable_const (1 : ℝ)).indicator (measurableSet_disagree z)) fun p => ?_
  by_cases hd : p ∈ disagree z
  · rw [Set.indicator_of_mem hd]
    exact measureReal_le_one
  · rw [Set.indicator_of_notMem hd]
    have h1 : ∀ᵐ w ∂(D.Q x p), w.1 z = p.1 z := by
      have := D.P_local x p.1 z hzx
      rw [← D.Q_fst x p] at this
      exact ae_of_ae_map measurable_fst.aemeasurable this
    have h2 : ∀ᵐ w ∂(D.Q x p), w.2 z = p.2 z := by
      have := D.P_local x p.2 z hzx
      rw [← D.Q_snd x p] at this
      exact ae_of_ae_map measurable_snd.aemeasurable this
    have h0 : D.Q x p (disagree z) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [h1, h2] with w hw1 hw2
      simp only [disagree, Set.mem_ofPred_eq, not_not] at hd ⊢
      rw [hw1, hw2, hd]
    simp [measureReal_def, h0]

/-- **At the updated site: the influence bound, integrated.** -/
theorem bind_disagree_le_self {π : Measure (Pair ι S)} [IsProbabilityMeasure π] (x : ι) :
    (π.bind (D.Q x)).real (disagree x) ≤ ∑ z, D.A x z * π.real (disagree z) := by
  rw [bind_real _ (measurableSet_disagree x)]
  calc ∫ p, (D.Q x p).real (disagree x) ∂π
      ≤ ∫ p, ∑ z, (disagree z).indicator (fun _ => D.A x z) p ∂π :=
        integral_mono (integrable_kernel_real _ (measurableSet_disagree x))
          (integrable_finsetSum _ fun z _ => (integrable_const _).indicator (measurableSet_disagree z))
          fun p => D.influence x p
    _ = ∑ z, D.A x z * π.real (disagree z) := by
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl fun z _ => by
            rw [integral_indicator_const _ (measurableSet_disagree z), smul_eq_mul, mul_comm]
        · exact fun z _ => (integrable_const _).indicator (measurableSet_disagree z)

end SiteDynamics

/-! ### From a coupling to total variation -/

section TV

variable [MeasurableEq S]

/-- `{p | p.1 ∈ s} ⊆ {p | p.2 ∈ s} ∪ ⋃_z {p.1 z ≠ p.2 z}`. -/
theorem fst_preimage_subset (s : Set (ι → S)) :
    Prod.fst ⁻¹' s ⊆ Prod.snd ⁻¹' s ∪ ⋃ z ∈ (univ : Finset ι), disagree (S := S) z := by
  intro p hp
  by_cases h : p.2 ∈ s
  · exact Or.inl h
  · right
    have hne : p.1 ≠ p.2 := fun he => h (he ▸ hp)
    obtain ⟨z, hz⟩ := Function.ne_iff.mp hne
    exact Set.mem_biUnion (Finset.mem_univ z) hz

theorem snd_preimage_subset (s : Set (ι → S)) :
    Prod.snd ⁻¹' s ⊆ Prod.fst ⁻¹' s ∪ ⋃ z ∈ (univ : Finset ι), disagree (S := S) z := by
  intro p hp
  by_cases h : p.1 ∈ s
  · exact Or.inl h
  · right
    have hne : p.1 ≠ p.2 := fun he => h (he ▸ hp)
    obtain ⟨z, hz⟩ := Function.ne_iff.mp hne
    exact Set.mem_biUnion (Finset.mem_univ z) hz

/-- **The coupling inequality.** For a coupling `π` of `ν` and `ν'` and a measurable `s`:
`|ν(s) - ν'(s)| ≤ Σ_z π(p.1 z ≠ p.2 z) = Φ_1(π)`. -/
theorem abs_sub_le_phi {π : Measure (Pair ι S)} [IsProbabilityMeasure π] {s : Set (ι → S)} (hs : MeasurableSet s) :
    |(π.map Prod.fst).real s - (π.map Prod.snd).real s| ≤ phi (fun _ => 1) π := by
  rw [map_measureReal_apply measurable_fst hs, map_measureReal_apply measurable_snd hs]
  have hU : π.real (⋃ z ∈ (univ : Finset ι), disagree (S := S) z) ≤ phi (fun _ => 1) π := by
    simp only [phi, one_mul]
    exact measureReal_biUnion_finset_le _ _
  have h1 := (measureReal_mono (μ := π) (fst_preimage_subset (ι := ι) s)).trans (measureReal_union_le (μ := π) _ _)
  have h2 := (measureReal_mono (μ := π) (snd_preimage_subset (ι := ι) s)).trans (measureReal_union_le (μ := π) _ _)
  rw [abs_le]
  constructor <;> linarith

theorem phi_one_le_card {π : Measure (Pair ι S)} [IsProbabilityMeasure π] :
    phi (fun _ => (1 : ℝ)) π ≤ Fintype.card ι := by
  simp only [phi, one_mul]
  calc ∑ z, π.real (disagree (S := S) z) ≤ ∑ _z : ι, (1 : ℝ) := Finset.sum_le_sum fun z _ => measureReal_le_one
    _ = _ := by simp

end TV

/-! ### Systematic scan -/

namespace SiteDynamics

variable {μ : Measure (ι → S)} (D : SiteDynamics μ)

/-- One sweep of the sampler: update the sites of `order` in turn. -/
def sweep (order : List ι) (ν : Measure (ι → S)) : Measure (ι → S) :=
  order.foldl (fun ν x => ν.bind (D.P x)) ν

/-- One sweep of the coupled chain. -/
def sweepC (order : List ι) (π : Measure (Pair ι S)) : Measure (Pair ι S) :=
  order.foldl (fun π x => π.bind (D.Q x)) π

theorem sweepC_map_fst (order : List ι) (π : Measure (Pair ι S)) :
    (D.sweepC order π).map Prod.fst = D.sweep order (π.map Prod.fst) := by
  induction order generalizing π with
  | nil => rfl
  | cons x l ih =>
      simp only [sweepC, sweep, List.foldl_cons] at ih ⊢
      rw [ih, D.bind_map_fst]

theorem sweepC_map_snd (order : List ι) (π : Measure (Pair ι S)) :
    (D.sweepC order π).map Prod.snd = D.sweep order (π.map Prod.snd) := by
  induction order generalizing π with
  | nil => rfl
  | cons x l ih =>
      simp only [sweepC, sweep, List.foldl_cons] at ih ⊢
      rw [ih, D.bind_map_snd]

theorem sweep_inv (order : List ι) : D.sweep order μ = μ := by
  induction order with
  | nil => rfl
  | cons x l ih =>
      simp only [sweep, List.foldl_cons] at ih ⊢
      rw [D.P_inv, ih]

theorem isProbabilityMeasure_sweepC (order : List ι) (π : Measure (Pair ι S)) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (D.sweepC order π) := by
  induction order generalizing π with
  | nil => simpa [sweepC]
  | cons x l ih =>
      simp only [sweepC, List.foldl_cons] at ih ⊢
      have := isProbabilityMeasure_bind (π := π) (D.Q x)
      exact ih _

variable [MeasurableEq S]

/-- **Gauss-Seidel invariant.** If every disagreement probability is at most `δ`, those of the sites in `M` at most
`α δ`, and every row sum of `A` is at most `α ≤ 1`, then after updating the sites of `l` in turn, every disagreement
probability is at most `δ` and those of the sites in `M ∪ l` at most `α δ`. -/
theorem sweepC_disagree_le (l : List ι) {α δ : ℝ} (hα : α ≤ 1) (hδ : 0 ≤ δ) (hrow : ∀ x, ∑ z, D.A x z ≤ α)
    (M : Set ι) (π : Measure (Pair ι S)) [IsProbabilityMeasure π]
    (hall : ∀ z, π.real (disagree z) ≤ δ) (hM : ∀ z ∈ M, π.real (disagree z) ≤ α * δ) :
    (∀ z, (D.sweepC l π).real (disagree z) ≤ δ) ∧
      (∀ z, (z ∈ M ∨ z ∈ l) → (D.sweepC l π).real (disagree z) ≤ α * δ) := by
  induction l generalizing π M with
  | nil => exact ⟨hall, fun z hz => hM z (hz.resolve_right (List.not_mem_nil))⟩
  | cons x l ih =>
      simp only [sweepC, List.foldl_cons]
      have := isProbabilityMeasure_bind (π := π) (D.Q x)
      have hx : (π.bind (D.Q x)).real (disagree x) ≤ α * δ := by
        calc (π.bind (D.Q x)).real (disagree x) ≤ ∑ z, D.A x z * π.real (disagree z) := D.bind_disagree_le_self x
          _ ≤ ∑ z, D.A x z * δ := Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hall z) (D.A_nonneg x z)
          _ = (∑ z, D.A x z) * δ := by rw [Finset.sum_mul]
          _ ≤ α * δ := mul_le_mul_of_nonneg_right (hrow x) hδ
      have hall' : ∀ z, (π.bind (D.Q x)).real (disagree z) ≤ δ := fun z => by
        by_cases hzx : z = x
        · subst hzx
          have : α * δ ≤ δ := by nlinarith
          linarith
        · exact (D.bind_disagree_le_of_ne hzx).trans (hall z)
      have hM' : ∀ z ∈ insert x M, (π.bind (D.Q x)).real (disagree z) ≤ α * δ := fun z hz => by
        rcases hz with hzx | hzM
        · rw [hzx]; exact hx
        · by_cases hzx : z = x
          · rw [hzx]; exact hx
          · exact (D.bind_disagree_le_of_ne hzx).trans (hM z hzM)
      obtain ⟨h1, h2⟩ := ih (insert x M) (π.bind (D.Q x)) hall' hM'
      refine ⟨h1, fun z hz => h2 z ?_⟩
      rcases hz with hz | hz
      · exact Or.inl (Set.mem_insert_of_mem x hz)
      · rcases List.mem_cons.mp hz with hz | hz
        · exact Or.inl (hz ▸ Set.mem_insert z M)
        · exact Or.inr hz

/-- **One sweep contracts the largest disagreement probability by `α`.** -/
theorem sweepC_contract {order : List ι} (hcover : ∀ x, x ∈ order) {α δ : ℝ} (hα : α ≤ 1) (hδ : 0 ≤ δ)
    (hrow : ∀ x, ∑ z, D.A x z ≤ α) (π : Measure (Pair ι S)) [IsProbabilityMeasure π]
    (hall : ∀ z, π.real (disagree z) ≤ δ) : ∀ z, (D.sweepC order π).real (disagree z) ≤ α * δ := fun z =>
  (D.sweepC_disagree_le order hα hδ hrow ∅ π hall (fun z hz => absurd hz (Set.notMem_empty z))).2 z
    (Or.inr (hcover z))

/-- `t` sweeps of the coupled chain from `ν ⊗ μ`. -/
def sweepsC (order : List ι) (ν : Measure (ι → S)) (t : ℕ) : Measure (Pair ι S) :=
  (D.sweepC order)^[t] (ν.prod μ)

theorem isProbabilityMeasure_sweepsC (order : List ι) (ν : Measure (ι → S)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] (t : ℕ) : IsProbabilityMeasure (D.sweepsC order ν t) := by
  induction t with
  | zero => simp only [sweepsC, Function.iterate_zero, id]; infer_instance
  | succ t ih =>
      simp only [sweepsC, Function.iterate_succ_apply'] at ih ⊢
      exact D.isProbabilityMeasure_sweepC order _

theorem sweepsC_map_fst (order : List ι) (ν : Measure (ι → S)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (t : ℕ) : (D.sweepsC order ν t).map Prod.fst = (D.sweep order)^[t] ν := by
  induction t with
  | zero => simp [sweepsC]
  | succ t ih =>
      simp only [sweepsC, Function.iterate_succ_apply'] at ih ⊢
      rw [sweepC_map_fst, ih]

theorem sweepsC_map_snd (order : List ι) (ν : Measure (ι → S)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (t : ℕ) : (D.sweepsC order ν t).map Prod.snd = μ := by
  induction t with
  | zero => simp [sweepsC]
  | succ t ih =>
      simp only [sweepsC, Function.iterate_succ_apply'] at ih ⊢
      rw [sweepC_map_snd, ih, sweep_inv]

theorem sweepsC_disagree_le {order : List ι} (hcover : ∀ x, x ∈ order) {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1)
    (hrow : ∀ x, ∑ z, D.A x z ≤ α) (ν : Measure (ι → S)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (t : ℕ) : ∀ z, (D.sweepsC order ν t).real (disagree z) ≤ α ^ t := by
  induction t with
  | zero =>
      intro z
      simp only [sweepsC, Function.iterate_zero, id, pow_zero]
      exact measureReal_le_one
  | succ t ih =>
      have := D.isProbabilityMeasure_sweepsC order ν t
      intro z
      have h := D.sweepC_contract hcover hα (pow_nonneg hα0 t) hrow (D.sweepsC order ν t) ih z
      simp only [sweepsC, Function.iterate_succ_apply'] at h ⊢
      rw [pow_succ, mul_comm]
      exact h

/-- **Systematic scan: total variation after `t` sweeps is at most `n α^t`** (row sums of the influence matrix at
most `α ≤ 1`; every site in the scan). -/
theorem tv_sweep_le {order : List ι} (hcover : ∀ x, x ∈ order) {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1)
    (hrow : ∀ x, ∑ z, D.A x z ≤ α) (ν : Measure (ι → S)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (t : ℕ) {s : Set (ι → S)} (hs : MeasurableSet s) :
    |((D.sweep order)^[t] ν).real s - μ.real s| ≤ Fintype.card ι * α ^ t := by
  have := D.isProbabilityMeasure_sweepsC order ν t
  have h := abs_sub_le_phi (π := D.sweepsC order ν t) hs
  rw [D.sweepsC_map_fst, D.sweepsC_map_snd] at h
  refine h.trans ?_
  simp only [phi, one_mul]
  calc ∑ z, (D.sweepsC order ν t).real (disagree z) ≤ ∑ _z : ι, α ^ t :=
        Finset.sum_le_sum fun z _ => D.sweepsC_disagree_le hcover hα0 hα hrow ν t z
    _ = _ := by simp

/-- **Systematic scan, test functions** (through M1's `abs_integral_sub_le_phi`). -/
theorem integral_sweep_le {order : List ι} (hcover : ∀ x, x ∈ order) {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1)
    (hrow : ∀ x, ∑ z, D.A x z ≤ α) (ν : Measure (ι → S)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (t : ℕ) {F : (ι → S) → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ σ, |F σ| ≤ M) :
    |∫ σ, F σ ∂((D.sweep order)^[t] ν) - ∫ σ, F σ ∂μ| ≤ 2 * M * (Fintype.card ι * α ^ t) := by
  have := D.isProbabilityMeasure_sweepsC order ν t
  have h := abs_integral_sub_le_phi (D.sweepsC_map_fst order ν t) (D.sweepsC_map_snd order ν t)
    (v := fun _ => 1) (fun _ => zero_le_one) univ one_pos (fun _ _ => le_rfl) hF hFM
    (fun σ σ' hσ => congrArg F (funext fun x => hσ x (Finset.mem_univ x)))
  obtain ⟨σ₀, -⟩ := nonempty_of_measure_ne_zero (μ := ν) (s := Set.univ) (by simp)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hFM σ₀)
  refine h.trans ?_
  rw [inv_one, mul_one]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  simp only [phi, one_mul]
  calc ∑ z, (D.sweepsC order ν t).real (disagree z) ≤ ∑ _z : ι, α ^ t :=
        Finset.sum_le_sum fun z _ => D.sweepsC_disagree_le hcover hα0 hα hrow ν t z
    _ = _ := by simp

end SiteDynamics

/-! ### Random scan -/

/-- The uniform average of a family of measures. -/
def avg {α : Type*} [MeasurableSpace α] (f : ι → Measure α) : Measure α := ((Fintype.card ι : ℝ≥0∞)⁻¹) • ∑ x, f x

namespace SiteDynamics

variable {μ : Measure (ι → S)} (D : SiteDynamics μ)

/-- One random-scan step: pick a site uniformly and update it. -/
def rsStep (ν : Measure (ι → S)) : Measure (ι → S) := avg fun x => ν.bind (D.P x)

/-- One coupled random-scan step (both chains update the same site): M1's averaged update `T`, one-site blocks. -/
def rsStepC (π : Measure (Pair ι S)) : Measure (Pair ι S) := avg fun x => π.bind (D.Q x)

theorem avg_apply {α : Type*} [MeasurableSpace α] (f : ι → Measure α) (s : Set α) :
    avg f s = (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ x, f x s := by
  simp [avg, Measure.coe_finsetSum]

theorem card_inv_mul_card [Nonempty ι] (a : ℝ≥0∞) : (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ _x : ι, a = a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (by simp), one_mul]

theorem rsStepC_map_fst (π : Measure (Pair ι S)) : (D.rsStepC π).map Prod.fst = D.rsStep (π.map Prod.fst) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, rsStepC, rsStep, avg_apply, avg_apply]
  simp_rw [← Measure.map_apply measurable_fst hs, D.bind_map_fst]

theorem rsStepC_map_snd (π : Measure (Pair ι S)) : (D.rsStepC π).map Prod.snd = D.rsStep (π.map Prod.snd) := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs, rsStepC, rsStep, avg_apply, avg_apply]
  simp_rw [← Measure.map_apply measurable_snd hs, D.bind_map_snd]

theorem rsStep_inv [Nonempty ι] : D.rsStep μ = μ := by
  ext s hs
  rw [rsStep, avg_apply]
  simp_rw [D.P_inv]
  exact card_inv_mul_card _

theorem isProbabilityMeasure_rsStepC [Nonempty ι] (π : Measure (Pair ι S)) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (D.rsStepC π) := by
  constructor
  rw [rsStepC, avg_apply]
  have : ∀ x, π.bind (D.Q x) Set.univ = 1 := fun x => by
    have := isProbabilityMeasure_bind (π := π) (D.Q x)
    exact measure_univ
  simp_rw [this]
  exact card_inv_mul_card _

theorem rsStepC_real [Nonempty ι] (π : Measure (Pair ι S)) [IsProbabilityMeasure π] (s : Set (Pair ι S)) :
    (D.rsStepC π).real s = (Fintype.card ι : ℝ)⁻¹ * ∑ x, (π.bind (D.Q x)).real s := by
  have hp : ∀ x, IsProbabilityMeasure (π.bind (D.Q x)) := fun x => isProbabilityMeasure_bind (D.Q x)
  rw [measureReal_def, rsStepC, avg_apply, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun x _ => measure_ne_top _ _)]
  rfl

variable [MeasurableEq S]

/-- **One random-scan step contracts `Φ` by `1 - (1 - α)/n`** (column sums of the influence matrix at most `α`).
This is M1's `phi_T_le` for one-site blocks, without its stationarity: the coupling's marginals are arbitrary. -/
theorem phi_rsStepC_le [Nonempty ι] {α : ℝ} (hcol : ∀ z, ∑ x, D.A x z ≤ α) (π : Measure (Pair ι S))
    [IsProbabilityMeasure π] :
    phi (fun _ => 1) (D.rsStepC π) ≤ (1 - (1 - α) / Fintype.card ι) * phi (fun _ => 1) π := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  set d : ι → ℝ := fun z => π.real (disagree (S := S) z) with hd
  have hd0 : ∀ z, 0 ≤ d z := fun z => measureReal_nonneg
  have hΦ : phi (fun _ => 1) π = ∑ z, d z := by simp [phi, hd]
  -- one site
  have hone : ∀ x, ∑ z, (π.bind (D.Q x)).real (disagree (S := S) z) ≤
      ∑ z, d z - d x + ∑ z, D.A x z * d z := fun x => by
    have := isProbabilityMeasure_bind (π := π) (D.Q x)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), ← Finset.add_sum_erase _ d (Finset.mem_univ x)]
    have h1 : ∑ z ∈ univ.erase x, (π.bind (D.Q x)).real (disagree (S := S) z) ≤ ∑ z ∈ univ.erase x, d z :=
      Finset.sum_le_sum fun z hz => D.bind_disagree_le_of_ne (Finset.ne_of_mem_erase hz)
    have h2 := D.bind_disagree_le_self (π := π) x
    linarith
  have hsum : ∑ x, ∑ z, D.A x z * d z ≤ α * ∑ z, d z := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hcol z) (hd0 z)
  have htot : ∑ x, ∑ z, (π.bind (D.Q x)).real (disagree (S := S) z) ≤
      (Fintype.card ι : ℝ) * ∑ z, d z - ∑ z, d z + α * ∑ z, d z := by
    calc _ ≤ ∑ x, (∑ z, d z - d x + ∑ z, D.A x z * d z) := Finset.sum_le_sum fun x _ => hone x
      _ = (Fintype.card ι : ℝ) * ∑ z, d z - ∑ z, d z + ∑ x, ∑ z, D.A x z * d z := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := by linarith
  have hT : phi (fun _ => 1) (D.rsStepC π) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ x, ∑ z, (π.bind (D.Q x)).real (disagree (S := S) z) := by
    simp only [phi, one_mul, D.rsStepC_real, ← Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hT, hΦ]
  calc (Fintype.card ι : ℝ)⁻¹ * ∑ x, ∑ z, (π.bind (D.Q x)).real (disagree (S := S) z)
      ≤ (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * ∑ z, d z - ∑ z, d z + α * ∑ z, d z) :=
        mul_le_mul_of_nonneg_left htot (inv_nonneg.mpr hN.le)
    _ = _ := by field_simp; ring

/-- `k` random-scan steps of the coupled chain from `ν ⊗ μ`. -/
def rsStepsC (ν : Measure (ι → S)) (k : ℕ) : Measure (Pair ι S) := D.rsStepC^[k] (ν.prod μ)

theorem isProbabilityMeasure_rsStepsC [Nonempty ι] (ν : Measure (ι → S)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] (k : ℕ) : IsProbabilityMeasure (D.rsStepsC ν k) := by
  induction k with
  | zero => simp only [rsStepsC, Function.iterate_zero, id]; infer_instance
  | succ k ih =>
      simp only [rsStepsC, Function.iterate_succ_apply'] at ih ⊢
      exact D.isProbabilityMeasure_rsStepC _

theorem rsStepsC_map_fst (ν : Measure (ι → S)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (k : ℕ) :
    (D.rsStepsC ν k).map Prod.fst = D.rsStep^[k] ν := by
  induction k with
  | zero => simp [rsStepsC]
  | succ k ih =>
      simp only [rsStepsC, Function.iterate_succ_apply'] at ih ⊢
      rw [rsStepC_map_fst, ih]

theorem rsStepsC_map_snd [Nonempty ι] (ν : Measure (ι → S)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (k : ℕ) : (D.rsStepsC ν k).map Prod.snd = μ := by
  induction k with
  | zero => simp [rsStepsC]
  | succ k ih =>
      simp only [rsStepsC, Function.iterate_succ_apply'] at ih ⊢
      rw [rsStepC_map_snd, ih, rsStep_inv]

theorem phi_rsStepsC_le [Nonempty ι] {α : ℝ} (hα0 : 0 ≤ α) (hcol : ∀ z, ∑ x, D.A x z ≤ α)
    (ν : Measure (ι → S)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (k : ℕ) :
    phi (fun _ => 1) (D.rsStepsC ν k) ≤ Fintype.card ι * (1 - (1 - α) / Fintype.card ι) ^ k := by
  have hN : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.mpr Fintype.card_pos
  have hθ : 0 ≤ 1 - (1 - α) / Fintype.card ι := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  induction k with
  | zero => simpa [rsStepsC] using phi_one_le_card (π := ν.prod μ)
  | succ k ih =>
      have := D.isProbabilityMeasure_rsStepsC ν k
      have h := D.phi_rsStepC_le hcol (D.rsStepsC ν k)
      simp only [rsStepsC, Function.iterate_succ_apply'] at h ih ⊢
      calc _ ≤ _ := h
        _ ≤ (1 - (1 - α) / Fintype.card ι) * (Fintype.card ι * (1 - (1 - α) / Fintype.card ι) ^ k) :=
            mul_le_mul_of_nonneg_left ih hθ
        _ = _ := by ring

/-- **Random scan: total variation after `k` single-site steps** is at most `n (1 - (1 - α)/n)^k` (column sums of
the influence matrix at most `α`). -/
theorem tv_rs_le [Nonempty ι] {α : ℝ} (hα0 : 0 ≤ α) (hcol : ∀ z, ∑ x, D.A x z ≤ α)
    (ν : Measure (ι → S)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (k : ℕ)
    {s : Set (ι → S)} (hs : MeasurableSet s) :
    |(D.rsStep^[k] ν).real s - μ.real s| ≤ Fintype.card ι * (1 - (1 - α) / Fintype.card ι) ^ k := by
  have := D.isProbabilityMeasure_rsStepsC ν k
  have h := abs_sub_le_phi (π := D.rsStepsC ν k) hs
  rw [D.rsStepsC_map_fst, D.rsStepsC_map_snd] at h
  exact h.trans (D.phi_rsStepsC_le hα0 hcol ν k)

/-- **Random scan, test functions** (through M1's `abs_integral_sub_le_phi`). -/
theorem integral_rs_le [Nonempty ι] {α : ℝ} (hα0 : 0 ≤ α) (hcol : ∀ z, ∑ x, D.A x z ≤ α)
    (ν : Measure (ι → S)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (k : ℕ)
    {F : (ι → S) → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ σ, |F σ| ≤ M) :
    |∫ σ, F σ ∂(D.rsStep^[k] ν) - ∫ σ, F σ ∂μ| ≤
      2 * M * (Fintype.card ι * (1 - (1 - α) / Fintype.card ι) ^ k) := by
  have := D.isProbabilityMeasure_rsStepsC ν k
  have h := abs_integral_sub_le_phi (D.rsStepsC_map_fst ν k) (D.rsStepsC_map_snd ν k)
    (v := fun _ => 1) (fun _ => zero_le_one) univ one_pos (fun _ _ => le_rfl) hF hFM
    (fun σ σ' hσ => congrArg F (funext fun x => hσ x (Finset.mem_univ x)))
  obtain ⟨σ₀, -⟩ := nonempty_of_measure_ne_zero (μ := ν) (s := Set.univ) (by simp)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hFM σ₀)
  refine h.trans ?_
  rw [inv_one, mul_one]
  exact mul_le_mul_of_nonneg_left (D.phi_rsStepsC_le hα0 hcol ν k) (by linarith)

end SiteDynamics

/-! ### Mixing times -/

/-- `n α^t ≤ ε` as soon as `t log(1/α) ≥ log(n/ε)`. -/
theorem card_mul_pow_le {n α ε : ℝ} (hn : 0 < n) (hα0 : 0 < α) (hε : 0 < ε) {t : ℕ}
    (ht : Real.log (n / ε) ≤ t * Real.log α⁻¹) : n * α ^ t ≤ ε := by
  have h1 : α ^ t = Real.exp (-(t * Real.log α⁻¹)) := by
    rw [Real.log_inv, mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log hα0]
  have h2 : Real.exp (-(t * Real.log α⁻¹)) ≤ Real.exp (-Real.log (n / ε)) := Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-Real.log (n / ε)) = ε / n := by
    rw [Real.exp_neg, Real.exp_log (div_pos hn hε), inv_div]
  rw [h3] at h2
  rw [h1]
  calc n * Real.exp (-(t * Real.log α⁻¹)) ≤ n * (ε / n) := mul_le_mul_of_nonneg_left h2 hn.le
    _ = ε := by field_simp

/-- `(1 - c/n)^k ≤ e^{-c k/n}`. -/
theorem one_sub_div_pow_le {c n : ℝ} (h : 0 ≤ 1 - c / n) (k : ℕ) :
    (1 - c / n) ^ k ≤ Real.exp (-(c * k / n)) := by
  have h1 : 1 - c / n ≤ Real.exp (-(c / n)) := by
    have := Real.add_one_le_exp (-(c / n))
    linarith
  calc (1 - c / n) ^ k ≤ Real.exp (-(c / n)) ^ k := pow_le_pow_left₀ h h1 k
    _ = Real.exp (-(c * k / n)) := by
        rw [← Real.exp_nat_mul]; congr 1; ring

/-- `n e^{-c k/n} ≤ ε` as soon as `c k ≥ n log(n/ε)`. -/
theorem card_mul_exp_le {n c ε : ℝ} (hn : 0 < n) (hε : 0 < ε) {k : ℕ}
    (hk : n * Real.log (n / ε) ≤ c * k) : n * Real.exp (-(c * k / n)) ≤ ε := by
  have h2 : Real.exp (-(c * k / n)) ≤ Real.exp (-Real.log (n / ε)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    rw [le_div_iff₀ hn, mul_comm]
    exact hk
  have h3 : Real.exp (-Real.log (n / ε)) = ε / n := by
    rw [Real.exp_neg, Real.exp_log (div_pos hn hε), inv_div]
  rw [h3] at h2
  calc n * Real.exp (-(c * k / n)) ≤ n * (ε / n) := mul_le_mul_of_nonneg_left h2 hn.le
    _ = ε := by field_simp

namespace SiteDynamics

variable {μ : Measure (ι → S)} (D : SiteDynamics μ) [MeasurableEq S]

/-- **Mixing time, systematic scan.** With row sums of the influence matrix at most `α ∈ (0, 1)`: after
`t ≥ log(n/ε) / log(1/α)` sweeps the sampler is within `ε` of `μ` in total variation, from every start. That is
`O(log n)` sweeps, `O(n log n)` single-site updates. -/
theorem mixing_sweep [Nonempty ι] {order : List ι} (hcover : ∀ x, x ∈ order) {α : ℝ} (hα0 : 0 < α) (hα : α < 1)
    (hrow : ∀ x, ∑ z, D.A x z ≤ α) {ε : ℝ} (hε : 0 < ε) {t : ℕ}
    (ht : Real.log (Fintype.card ι / ε) ≤ t * Real.log α⁻¹)
    (ν : Measure (ι → S)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] {s : Set (ι → S)}
    (hs : MeasurableSet s) : |((D.sweep order)^[t] ν).real s - μ.real s| ≤ ε :=
  (D.tv_sweep_le hcover hα0.le hα.le hrow ν t hs).trans
    (card_mul_pow_le (Nat.cast_pos.mpr Fintype.card_pos) hα0 hε ht)

/-- **Mixing time, random scan.** With column sums of the influence matrix at most `α < 1`: after
`k ≥ n log(n/ε) / (1 - α)` single-site steps the sampler is within `ε` of `μ` in total variation, from every start.
That is `O(n log n)` single-site updates. -/
theorem mixing_rs [Nonempty ι] {α : ℝ} (hα0 : 0 ≤ α) (hcol : ∀ z, ∑ x, D.A x z ≤ α)
    {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : Fintype.card ι * Real.log (Fintype.card ι / ε) ≤ (1 - α) * k)
    (ν : Measure (ι → S)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] {s : Set (ι → S)}
    (hs : MeasurableSet s) : |(D.rsStep^[k] ν).real s - μ.real s| ≤ ε := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hθ : 0 ≤ 1 - (1 - α) / Fintype.card ι := by
    have : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.mpr Fintype.card_pos
    rw [sub_nonneg, div_le_one hN]
    linarith
  calc _ ≤ Fintype.card ι * (1 - (1 - α) / Fintype.card ι) ^ k := D.tv_rs_le hα0 hcol ν k hs
    _ ≤ Fintype.card ι * Real.exp (-((1 - α) * k / Fintype.card ι)) :=
        mul_le_mul_of_nonneg_left (one_sub_div_pow_le hθ k) hN.le
    _ ≤ ε := card_mul_exp_le hN hε hk

end SiteDynamics

end ProofPhase.Mixing
