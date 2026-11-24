/-
Proof phase (round 5), workstream 3 (the quantum half): Lemma T in Lean (2026-11-22). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/r2-stepscaling/NOTE.md` §4 (Lemma T, paper);
`docs/mass-gap/weak-coupling/proof-phase/ws3-quantum/NOTE.md` (this workstream).
-/

import ProofPhase.Objects
import OneScale.Effective.Robust

/-!
# Lemma T: relative closeness of laws survives every blocking and passes to every conditional law

**The notion.** Two measures are **`ε`-relatively close**, `RelClose ε μ μ'`, if `μ' ≤ e^ε μ` and `μ ≤ e^ε μ'` as
measures (equivalently, for finite measures, `dμ'/dμ ∈ [e^{-ε}, e^{ε}]`). Densities whose logarithms differ by at most `ε`
everywhere give `ε`-relatively close measures (`relClose_withDensity`, `relClose_withDensity_log`).

**Lemma T (abstract, any measurable spaces; no Gibbs structure, no gauge theory).**
* **(a) blocking:** `RelClose.map` (any measurable map) and `RelClose.bind` (any Markov kernel, `Measure.bind`). By
  induction this covers any number of blocking steps, deterministic or noisy.
* **(b) conditional laws:** `relClose_normalize`: reweighting one measure by two weights `w, w'` with `w'/w ∈ [e^{-ε},
  e^{ε}]` and normalising gives `2ε`-relatively close laws. Applied to the block specifications of the R3 framework
  (`OneScale.locSpec`, the conditional law of a block `B` given the outside `σ`, density `∝ W(splice B σ ·)`),
  **`relClose_locSpec`**: if the two weights are `ε`-close, the conditional laws are `2ε`-close **at every boundary
  condition `σ`**, large-field boundaries included.
* **closeness of expectations:** `abs_integral_sub_le_of_relClose` (`|μ'(F) − μ(F)| ≤ (e^ε − 1) μ(|F|)`, any finite
  measures), `abs_integral_sub_le_osc` (probability measures, total oscillation `C`: `≤ (e^ε − 1) C`), and in the language
  of `OneScale.Effective`: `tvClose_locSpec` (`TVClose` with `e^{2ε} − 1`, uniformly in the boundary).

**Instantiation on the real objects (SU(2) Wilson, `ProofPhase.Objects`).**
* `relClose_wilsonMeasure`: the SU(2) Wilson measures at couplings `β, β'` on the same 4D torus are
  `4|β − β'| · #plaquettes`-relatively close (`weightMeasure` is a normalised reweighting of product Haar).
* `relClose_wilson_blocked`: hence so are their images under **every** measurable blocking (e.g. every `RPBlocking`),
  and every further blocking step (Lemma T(a)).
* `relClose_wilson_gaugeSpec`: the fine block specifications (conditional laws of a link set `B` given the rest) at
  `β, β'` are `4|β − β'| · #(plaquettes touching B)`-close at every boundary configuration: local, not extensive.

What is *not* here: the conditional laws of **image** variables are not given by explicit densities; for them Lemma
T(b) needs a choice of density version (`dμ'/dμ` clamped to `[e^{-ε}, e^{ε}]`), a Radon–Nikodym step not formalised
here (see the note). The per-volume chain (`ProofPhase.Quantum.PerVolume`) does not need it: it uses (a) and the
expectation bound only.
-/

open MeasureTheory Finset Filter Topology
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Quantum

/-! ## Relative closeness -/

/-- `e^ε` as a non-negative real. -/
def expNN (ε : ℝ) : ℝ≥0 := ⟨Real.exp ε, (Real.exp_pos ε).le⟩

@[simp] theorem coe_expNN (ε : ℝ) : ((expNN ε : ℝ≥0) : ℝ) = Real.exp ε := rfl

theorem expNN_ennreal (ε : ℝ) : ((expNN ε : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (Real.exp ε) := by
  rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (Real.exp_pos ε).le]; rfl

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Relative closeness of measures**: `μ' ≤ e^ε μ` and `μ ≤ e^ε μ'`. -/
def RelClose (ε : ℝ) (μ μ' : Measure α) : Prop := μ' ≤ expNN ε • μ ∧ μ ≤ expNN ε • μ'

theorem RelClose.symm {ε : ℝ} {μ μ' : Measure α} (h : RelClose ε μ μ') : RelClose ε μ' μ := ⟨h.2, h.1⟩

theorem relClose_refl {ε : ℝ} (hε : 0 ≤ ε) (μ : Measure α) : RelClose ε μ μ := by
  have : μ ≤ expNN ε • μ := by
    rw [Measure.le_iff]
    intro s _
    rw [Measure.coe_nnreal_smul_apply]
    calc μ s = 1 * μ s := (one_mul _).symm
      _ ≤ _ := by
        gcongr
        rw [← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
        simpa using Real.one_le_exp hε
  exact ⟨this, this⟩

/-! ## Lemma T (a): every blocking step -/

/-- **Lemma T(a), deterministic blocking.** Relative closeness passes to the images under any measurable map. -/
theorem RelClose.map {ε : ℝ} {μ μ' : Measure α} (h : RelClose ε μ μ') {f : α → β} (hf : Measurable f) :
    RelClose ε (μ.map f) (μ'.map f) := by
  have key : ∀ ν ν' : Measure α, ν' ≤ expNN ε • ν → ν'.map f ≤ expNN ε • ν.map f := by
    intro ν ν' hle
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.coe_nnreal_smul_apply, Measure.map_apply hf hs, Measure.map_apply hf hs]
    have := (Measure.le_iff.1 hle) _ (hf hs)
    rwa [Measure.coe_nnreal_smul_apply] at this
  exact ⟨key μ μ' h.1, key μ' μ h.2⟩

/-- **Lemma T(a), noisy blocking.** Relative closeness passes to the images under any Markov kernel
(`μ.bind κ`, the law of a configuration drawn from `κ(x, ·)` with `x ~ μ`). -/
theorem RelClose.bind {ε : ℝ} {μ μ' : Measure α} (h : RelClose ε μ μ') (κ : ProbabilityTheory.Kernel α β) :
    RelClose ε (μ.bind κ) (μ'.bind κ) := by
  have key : ∀ ν ν' : Measure α, ν' ≤ expNN ε • ν → ν'.bind κ ≤ expNN ε • ν.bind κ := by
    intro ν ν' hle
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.coe_nnreal_smul_apply, Measure.bind_apply hs κ.measurable.aemeasurable,
      Measure.bind_apply hs κ.measurable.aemeasurable]
    calc ∫⁻ a, κ a s ∂ν' ≤ ∫⁻ a, κ a s ∂(expNN ε • ν) := lintegral_mono' hle le_rfl
      _ = _ := by rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  exact ⟨key μ μ' h.1, key μ' μ h.2⟩

/-- Lemma T(a), iterated: any finite chain of blocking maps. -/
theorem RelClose.map_comp {γ : Type*} [MeasurableSpace γ] {ε : ℝ} {μ μ' : Measure α} (h : RelClose ε μ μ')
    {f : α → β} (hf : Measurable f) {g : β → γ} (hg : Measurable g) :
    RelClose ε (μ.map (g ∘ f)) (μ'.map (g ∘ f)) := by
  rw [← Measure.map_map hg hf, ← Measure.map_map hg hf]
  exact (h.map hf).map hg

/-! ## Densities -/

/-- **Relatively close densities give relatively close measures.** -/
theorem relClose_withDensity (ν : Measure α) {ε : ℝ} {ρ ρ' : α → ℝ≥0∞}
    (h1 : ∀ x, ρ' x ≤ expNN ε * ρ x) (h2 : ∀ x, ρ x ≤ expNN ε * ρ' x) :
    RelClose ε (ν.withDensity ρ) (ν.withDensity ρ') := by
  have key : ∀ σ σ' : α → ℝ≥0∞, (∀ x, σ' x ≤ expNN ε * σ x) →
      ν.withDensity σ' ≤ expNN ε • ν.withDensity σ := by
    intro σ σ' hσ
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.coe_nnreal_smul_apply, withDensity_apply _ hs, withDensity_apply _ hs,
      ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    exact lintegral_mono fun x => hσ x
  exact ⟨key ρ ρ' h1, key ρ' ρ h2⟩

theorem ofReal_le_expNN_mul {ε a b : ℝ} (hb : 0 ≤ b) (h : a ≤ Real.exp ε * b) :
    ENNReal.ofReal a ≤ (expNN ε : ℝ≥0∞) * ENNReal.ofReal b := by
  rw [expNN_ennreal, ← ENNReal.ofReal_mul (Real.exp_pos ε).le]
  exact ENNReal.ofReal_le_ofReal h

/-- **Densities with log-difference at most `ε` everywhere** (`a, b > 0`) give `ε`-relatively close measures. -/
theorem relClose_withDensity_log (ν : Measure α) {ε : ℝ} {ρ ρ' : α → ℝ} (hρ : ∀ x, 0 < ρ x) (hρ' : ∀ x, 0 < ρ' x)
    (h : ∀ x, |Real.log (ρ x) - Real.log (ρ' x)| ≤ ε) :
    RelClose ε (ν.withDensity fun x => ENNReal.ofReal (ρ x)) (ν.withDensity fun x => ENNReal.ofReal (ρ' x)) := by
  apply relClose_withDensity
  · intro x
    refine ofReal_le_expNN_mul (hρ x).le ?_
    have := (abs_le.1 (h x)).1
    calc ρ' x = Real.exp (Real.log (ρ' x)) := (Real.exp_log (hρ' x)).symm
      _ ≤ Real.exp (ε + Real.log (ρ x)) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp ε * ρ x := by rw [Real.exp_add, Real.exp_log (hρ x)]
  · intro x
    refine ofReal_le_expNN_mul (hρ' x).le ?_
    have := (abs_le.1 (h x)).2
    calc ρ x = Real.exp (Real.log (ρ x)) := (Real.exp_log (hρ x)).symm
      _ ≤ Real.exp (ε + Real.log (ρ' x)) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp ε * ρ' x := by rw [Real.exp_add, Real.exp_log (hρ' x)]

/-! ## Lemma T (b): normalised reweighting (conditional laws) -/

/-- The normalised reweighting of `q` by a weight `w`: `w / (∫ w dq) · q`. -/
def normalize (q : Measure α) (w : α → ℝ) : Measure α :=
  q.withDensity fun x => ENNReal.ofReal (w x / ∫ y, w y ∂q)

/-- **Lemma T(b), core.** If `w' ≤ e^ε w` and `w ≤ e^ε w'` pointwise (`w > 0`, both integrable, `∫ w dq > 0`), the
normalised reweightings are `2ε`-relatively close. -/
theorem relClose_normalize (q : Measure α) {ε : ℝ} {w w' : α → ℝ} (hw : ∀ x, 0 < w x) (hw' : ∀ x, 0 < w' x)
    (hi : Integrable w q) (hi' : Integrable w' q) (hZ : 0 < ∫ y, w y ∂q)
    (h1 : ∀ x, w' x ≤ Real.exp ε * w x) (h2 : ∀ x, w x ≤ Real.exp ε * w' x) :
    RelClose (2 * ε) (normalize q w) (normalize q w') := by
  have hZ1 : ∫ y, w' y ∂q ≤ Real.exp ε * ∫ y, w y ∂q := by
    rw [← integral_const_mul]; exact integral_mono hi' (hi.const_mul _) h1
  have hZ2 : ∫ y, w y ∂q ≤ Real.exp ε * ∫ y, w' y ∂q := by
    rw [← integral_const_mul]; exact integral_mono hi (hi'.const_mul _) h2
  unfold normalize
  generalize ∫ y, w y ∂q = Z at hZ hZ1 hZ2 ⊢
  generalize ∫ y, w' y ∂q = Z' at hZ1 hZ2 ⊢
  have he := Real.exp_pos ε
  have hZ' : 0 < Z' := by
    by_contra hne
    push_neg at hne
    have : Z ≤ 0 := hZ2.trans (mul_nonpos_of_nonneg_of_nonpos he.le hne)
    linarith
  have e2 : Real.exp (2 * ε) = Real.exp ε * Real.exp ε := by rw [← Real.exp_add]; ring_nf
  apply relClose_withDensity
  · intro x
    refine ofReal_le_expNN_mul (div_nonneg (hw x).le hZ.le) ?_
    rw [e2, div_le_iff₀ hZ']
    have h3 : w' x * Z ≤ Real.exp ε * w x * (Real.exp ε * Z') := by
      have := mul_le_mul (h1 x) hZ2 hZ.le (mul_pos (Real.exp_pos ε) (hw x)).le
      linarith
    calc w' x = w' x * Z / Z := by field_simp
      _ ≤ Real.exp ε * w x * (Real.exp ε * Z') / Z := div_le_div_of_nonneg_right h3 hZ.le
      _ = _ := by ring
  · intro x
    refine ofReal_le_expNN_mul (div_nonneg (hw' x).le hZ'.le) ?_
    rw [e2, div_le_iff₀ hZ]
    have h3 : w x * Z' ≤ Real.exp ε * w' x * (Real.exp ε * Z) := by
      have := mul_le_mul (h2 x) hZ1 hZ'.le (mul_pos (Real.exp_pos ε) (hw' x)).le
      linarith
    calc w x = w x * Z' / Z' := by field_simp
      _ ≤ Real.exp ε * w' x * (Real.exp ε * Z) / Z' := div_le_div_of_nonneg_right h3 hZ'.le
      _ = _ := by ring

/-! ## Expectations under relatively close measures -/

theorem integral_le_of_le_smul {μ μ' : Measure α} [IsFiniteMeasure μ] {c : ℝ≥0} (h : μ' ≤ c • μ) {G : α → ℝ}
    (hGm : Measurable G) (hG0 : ∀ x, 0 ≤ G x) {M : ℝ} (hGM : ∀ x, G x ≤ M) :
    ∫ x, G x ∂μ' ≤ c * ∫ x, G x ∂μ := by
  have hfin : IsFiniteMeasure μ' := isFiniteMeasure_of_le (c • μ) h
  have hint : Integrable G μ :=
    Integrable.of_bound hGm.aestronglyMeasurable M (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 x)]; exact hGM x)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hG0) hGm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hG0) hGm.aestronglyMeasurable]
  have hlt : ∫⁻ x, ENNReal.ofReal (G x) ∂μ ≠ ⊤ := (hint.lintegral_lt_top).ne
  calc (∫⁻ x, ENNReal.ofReal (G x) ∂μ').toReal ≤ (∫⁻ x, ENNReal.ofReal (G x) ∂(c • μ)).toReal :=
        ENNReal.toReal_mono (by rw [lintegral_smul_measure]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top hlt)
          (lintegral_mono' h le_rfl)
    _ = c * (∫⁻ x, ENNReal.ofReal (G x) ∂μ).toReal := by
        rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

/-- For nonnegative bounded `G`: `|μ'(G) − μ(G)| ≤ (e^ε − 1) μ(G)`. -/
theorem abs_integral_sub_le_nonneg {ε : ℝ} {μ μ' : Measure α} [IsFiniteMeasure μ] (h : RelClose ε μ μ')
    {G : α → ℝ} (hGm : Measurable G) (hG0 : ∀ x, 0 ≤ G x) {M : ℝ} (hGM : ∀ x, G x ≤ M) :
    |∫ x, G x ∂μ' - ∫ x, G x ∂μ| ≤ (Real.exp ε - 1) * ∫ x, G x ∂μ := by
  have hfin : IsFiniteMeasure μ' := isFiniteMeasure_of_le (expNN ε • μ) h.1
  have hup := integral_le_of_le_smul h.1 hGm hG0 hGM
  have hlo := integral_le_of_le_smul h.2 hGm hG0 hGM
  simp only [coe_expNN] at hup hlo
  have hI : 0 ≤ ∫ x, G x ∂μ := integral_nonneg hG0
  have he := Real.exp_pos ε
  generalize ∫ x, G x ∂μ = I at hup hlo hI ⊢
  generalize ∫ x, G x ∂μ' = I' at hup hlo ⊢
  rw [abs_le]
  constructor
  · have k1 : Real.exp ε * (I - I') ≤ (Real.exp ε - 1) * I := by linarith
    have k2 : (Real.exp ε - 1) * I ≤ Real.exp ε * ((Real.exp ε - 1) * I) := by
      nlinarith [mul_nonneg (sq_nonneg (Real.exp ε - 1)) hI]
    have := le_of_mul_le_mul_left (k1.trans k2) he
    linarith
  · linarith

/-- **Expectations under relatively close finite measures:** `|μ'(F) − μ(F)| ≤ (e^ε − 1) · μ(|F|)` for bounded
measurable `F`. -/
theorem abs_integral_sub_le_of_relClose {ε : ℝ} {μ μ' : Measure α} [IsFiniteMeasure μ] (h : RelClose ε μ μ')
    {F : α → ℝ} (hFm : Measurable F) {M : ℝ} (hFM : ∀ x, |F x| ≤ M) :
    |∫ x, F x ∂μ' - ∫ x, F x ∂μ| ≤ (Real.exp ε - 1) * ∫ x, |F x| ∂μ := by
  have hfin : IsFiniteMeasure μ' := isFiniteMeasure_of_le (expNN ε • μ) h.1
  set P : α → ℝ := fun x => max (F x) 0
  set Q : α → ℝ := fun x => max (-F x) 0
  have hPm : Measurable P := hFm.max measurable_const
  have hQm : Measurable Q := hFm.neg.max measurable_const
  have hP0 : ∀ x, 0 ≤ P x := fun x => le_max_right _ _
  have hQ0 : ∀ x, 0 ≤ Q x := fun x => le_max_right _ _
  have hPM : ∀ x, P x ≤ M := fun x => max_le ((le_abs_self _).trans (hFM x)) ((abs_nonneg _).trans (hFM x))
  have hQM : ∀ x, Q x ≤ M := fun x =>
    max_le ((neg_le_abs _).trans (hFM x)) ((abs_nonneg _).trans (hFM x))
  have hFPQ : ∀ x, F x = P x - Q x := fun x => by
    simp only [P, Q]; rcases le_total (F x) 0 with hx | hx
    · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
    · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
  have habs : ∀ x, |F x| = P x + Q x := fun x => by
    simp only [P, Q]; rcases le_total (F x) 0 with hx | hx
    · rw [max_eq_right hx, max_eq_left (by linarith), abs_of_nonpos hx]; ring
    · rw [max_eq_left hx, max_eq_right (by linarith), abs_of_nonneg hx]; ring
  have iP : ∀ ν : Measure α, IsFiniteMeasure ν → Integrable P ν := fun ν _ =>
    Integrable.of_bound hPm.aestronglyMeasurable M (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x)]; exact hPM x)
  have iQ : ∀ ν : Measure α, IsFiniteMeasure ν → Integrable Q ν := fun ν _ =>
    Integrable.of_bound hQm.aestronglyMeasurable M (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hQ0 x)]; exact hQM x)
  have eF : ∀ ν : Measure α, IsFiniteMeasure ν → ∫ x, F x ∂ν = ∫ x, P x ∂ν - ∫ x, Q x ∂ν := fun ν hν => by
    rw [← integral_sub (iP ν hν) (iQ ν hν)]; exact integral_congr_ae (Eventually.of_forall hFPQ)
  have eA : ∫ x, |F x| ∂μ = ∫ x, P x ∂μ + ∫ x, Q x ∂μ := by
    rw [← integral_add (iP μ inferInstance) (iQ μ inferInstance)]; exact integral_congr_ae (Eventually.of_forall habs)
  have h1 := abs_integral_sub_le_nonneg h hPm hP0 hPM
  have h2 := abs_integral_sub_le_nonneg h hQm hQ0 hQM
  rw [eF μ' hfin, eF μ inferInstance, eA]
  calc |∫ x, P x ∂μ' - ∫ x, Q x ∂μ' - (∫ x, P x ∂μ - ∫ x, Q x ∂μ)|
      = |(∫ x, P x ∂μ' - ∫ x, P x ∂μ) - (∫ x, Q x ∂μ' - ∫ x, Q x ∂μ)| := by ring_nf
    _ ≤ |∫ x, P x ∂μ' - ∫ x, P x ∂μ| + |∫ x, Q x ∂μ' - ∫ x, Q x ∂μ| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **Probability measures, total oscillation `C`:** `|μ'(F) − μ(F)| ≤ (e^ε − 1) C`. -/
theorem abs_integral_sub_le_osc [Nonempty α] {ε : ℝ} {μ μ' : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (h : RelClose ε μ μ') {F : α → ℝ} (hFm : Measurable F) (hFb : ∃ M, ∀ x, |F x| ≤ M) {C : ℝ}
    (hC : ∀ x x', |F x - F x'| ≤ C) :
    |∫ x, F x ∂μ' - ∫ x, F x ∂μ| ≤ (Real.exp ε - 1) * C := by
  obtain ⟨M, hM⟩ := hFb
  have hbdd : BddBelow (Set.range F) := ⟨-M, by rintro _ ⟨x, rfl⟩; exact (neg_le_of_abs_le (hM x))⟩
  set m := ⨅ x, F x
  have hm : ∀ x, m ≤ F x := fun x => ciInf_le hbdd x
  have hmC : ∀ x, F x - m ≤ C := by
    intro x
    have : F x - C ≤ m := le_ciInf fun x' => by have := (abs_le.1 (hC x x')).2; linarith
    linarith
  set G : α → ℝ := fun x => F x - m
  have hGm : Measurable G := hFm.sub measurable_const
  have hG0 : ∀ x, 0 ≤ G x := fun x => sub_nonneg.2 (hm x)
  have iF : ∀ ν : Measure α, IsProbabilityMeasure ν → Integrable F ν := fun ν _ =>
    Integrable.of_bound hFm.aestronglyMeasurable M (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hM x)
  have eG : ∀ ν : Measure α, IsProbabilityMeasure ν → ∫ x, G x ∂ν = ∫ x, F x ∂ν - m := fun ν hν => by
    rw [integral_sub (iF ν hν) (integrable_const m)]; simp
  have hG := abs_integral_sub_le_nonneg h hGm hG0 hmC
  rw [eG μ' inferInstance, eG μ inferInstance] at hG
  have hle : ∫ x, F x ∂μ - m ≤ C := by
    rw [← eG μ inferInstance]
    have := integral_mono (μ := μ) (Integrable.of_bound hGm.aestronglyMeasurable C (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 x)]; exact hmC x)) (integrable_const C) hmC
    simpa using this
  have hε : 1 ≤ Real.exp ε := by
    have := (Measure.le_iff.1 h.1) Set.univ MeasurableSet.univ
    rw [Measure.coe_nnreal_smul_apply, measure_univ, measure_univ, mul_one, ← ENNReal.coe_one,
      ENNReal.coe_le_coe] at this
    exact_mod_cast this
  calc |∫ x, F x ∂μ' - ∫ x, F x ∂μ| = |∫ x, F x ∂μ' - m - (∫ x, F x ∂μ - m)| := by ring_nf
    _ ≤ (Real.exp ε - 1) * (∫ x, F x ∂μ - m) := hG
    _ ≤ (Real.exp ε - 1) * C := mul_le_mul_of_nonneg_left hle (by linarith)

/-! ## Lemma T (b) for block specifications, every boundary condition -/

section Spec

open OneScale

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]

theorem locSpec_eq_normalize (B : Finset ι) (W : (ι → S) → ℝ) (σ : ι → S) :
    locSpec ν B W σ = normalize (prodMeasure ν) (fun ξ => W (splice B σ ξ)) := rfl

/-- **Lemma T(b) for block specifications.** If the weights satisfy `W' ≤ e^ε W` and `W ≤ e^ε W'` everywhere (both
local weights in the sense of `OneScale.LocalWeight`), then for **every** block `B` and **every** boundary condition
`σ` the conditional laws `q_B^σ` and `q'_B^σ` are `2ε`-relatively close. -/
theorem relClose_locSpec {W W' : (ι → S) → ℝ} (hW : LocalWeight W) (hW' : LocalWeight W') {ε : ℝ}
    (h1 : ∀ σ, W' σ ≤ Real.exp ε * W σ) (h2 : ∀ σ, W σ ≤ Real.exp ε * W' σ) (B : Finset ι) (σ : ι → S) :
    RelClose (2 * ε) (locSpec ν B W σ) (locSpec ν B W' σ) := by
  rw [locSpec_eq_normalize, locSpec_eq_normalize]
  exact relClose_normalize _ (fun ξ => hW.pos _) (fun ξ => hW'.pos _) (integrable_comp_splice hW.bm σ _)
    (integrable_comp_splice hW'.bm σ _) (hW.locZ_pos (ν := ν) (B := B) σ) (fun ξ => h1 _) (fun ξ => h2 _)

/-- **Lemma T(b) in the language of `OneScale.Effective`:** the block specifications are `TVClose` with
`e^{2ε} − 1`, uniformly in the boundary condition. -/
theorem tvClose_locSpec [Nonempty S] {W W' : (ι → S) → ℝ} (hW : LocalWeight W) (hW' : LocalWeight W') {ε : ℝ}
    (h1 : ∀ σ, W' σ ≤ Real.exp ε * W σ) (h2 : ∀ σ, W σ ≤ Real.exp ε * W' σ) (B : Finset ι) :
    Effective.TVClose B (locSpec ν B W') (locSpec ν B W) (Real.exp (2 * ε) - 1) := by
  intro σ F C hF _ hC
  have := hW.isProbabilityMeasure_locSpec (ν := ν) (B := B) σ
  have := hW'.isProbabilityMeasure_locSpec (ν := ν) (B := B) σ
  exact abs_integral_sub_le_osc (relClose_locSpec ν hW hW' h1 h2 B σ) hF.meas hF.bdd hC

end Spec

/-! ## Instantiation: SU(2) Wilson measures and their blockings -/

section Wilson

open AreaLaw.Concrete OneScale OneScale.Gauge Positivity

variable {N : ℕ} [NeZero N]

theorem wilson_plaqProd_eq (β : ℝ) (s : Finset (LatticePlaquette 4 N)) (U : GaugeConnection SU2 4 N) :
    plaqProd 2 (wilsonWeight β) s U = Real.exp (β * ∑ p ∈ s, xp 2 p U) := by
  unfold plaqProd wilsonWeight
  rw [Finset.mul_sum, Real.exp_sum]

theorem wilson_ratio_le (β β' : ℝ) (s : Finset (LatticePlaquette 4 N)) (U : GaugeConnection SU2 4 N) :
    plaqProd 2 (wilsonWeight β') s U ≤
      Real.exp (2 * |β - β'| * s.card) * plaqProd 2 (wilsonWeight β) s U := by
  rw [wilson_plaqProd_eq, wilson_plaqProd_eq, ← Real.exp_add, Real.exp_le_exp]
  have hb : |∑ p ∈ s, xp 2 p U| ≤ 2 * s.card := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ s, |xp 2 p U| ≤ ∑ p ∈ s, (2 : ℝ) :=
          sum_le_sum fun p _ => by
            have := OneScale.Gauge.abs_xp_le (n := 2) (G := SU2) (d := 4) (N := N)
              (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) p U
            exact_mod_cast this
      _ = 2 * s.card := by rw [sum_const, nsmul_eq_mul]; ring
  have : (β' - β) * ∑ p ∈ s, xp 2 p U ≤ |β - β'| * (2 * s.card) := by
    calc (β' - β) * ∑ p ∈ s, xp 2 p U ≤ |(β' - β) * ∑ p ∈ s, xp 2 p U| := le_abs_self _
      _ = |β - β'| * |∑ p ∈ s, xp 2 p U| := by rw [abs_mul, abs_sub_comm]
      _ ≤ |β - β'| * (2 * s.card) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  nlinarith

theorem localWeight_wilson (β : ℝ) (s : Finset (LatticePlaquette 4 N)) :
    LocalWeight (plaqProd (d := 4) (N := N) (G := SU2) 2 (wilsonWeight β) s) :=
  localWeight_plaqProd continuous_subtype_val (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
    (posWeight_wilson 2 β) s

theorem wilsonMeasure_eq_normalize (β : ℝ) :
    wilsonMeasure SU2 2 β 4 N =
      normalize (prodMeasure (haarG SU2)) (plaqProd (d := 4) (N := N) (G := SU2) 2 (wilsonWeight β) univ) := rfl

/-- **Lemma T on the real objects: SU(2) Wilson measures at two couplings.** On the 4D torus `(ℤ/Nℤ)⁴` the Wilson
measures at `β` and `β'` are `4|β − β'| · #plaquettes`-relatively close. (Extensive in the volume: a per-volume
statement.) -/
theorem relClose_wilsonMeasure (β β' : ℝ) :
    RelClose (2 * (2 * |β - β'| * (univ : Finset (LatticePlaquette 4 N)).card))
      (wilsonMeasure SU2 2 β 4 N) (wilsonMeasure SU2 2 β' 4 N) := by
  rw [wilsonMeasure_eq_normalize, wilsonMeasure_eq_normalize]
  have hW := localWeight_wilson (N := N) β univ
  have hW' := localWeight_wilson (N := N) β' univ
  have hZ : 0 < ∫ τ, plaqProd (d := 4) (N := N) (G := SU2) 2 (wilsonWeight β) univ τ ∂(prodMeasure (haarG SU2)) := by
    have hsp : ∀ ξ : GaugeConnection SU2 4 N, splice (univ : Finset (LatticeLink 4 N)) (fun _ => 1) ξ = ξ :=
      fun ξ => funext fun i => by simp only [splice, mem_univ, if_true]
    have := hW.locZ_pos (ν := haarG SU2) (B := (univ : Finset (LatticeLink 4 N))) (fun _ => 1)
    unfold locZ at this
    simp only [hsp] at this
    exact this
  have h1 : ∀ σ, plaqProd (d := 4) (N := N) (G := SU2) 2 (wilsonWeight β') univ σ ≤
      Real.exp (2 * |β - β'| * (univ : Finset (LatticePlaquette 4 N)).card) *
        plaqProd (d := 4) (N := N) (G := SU2) 2 (wilsonWeight β) univ σ := fun σ => wilson_ratio_le β β' univ σ
  have h2 : ∀ σ, plaqProd (d := 4) (N := N) (G := SU2) 2 (wilsonWeight β) univ σ ≤
      Real.exp (2 * |β - β'| * (univ : Finset (LatticePlaquette 4 N)).card) *
        plaqProd (d := 4) (N := N) (G := SU2) 2 (wilsonWeight β') univ σ := fun σ => by
    have := wilson_ratio_le β' β univ σ; rwa [abs_sub_comm] at this
  have i1 := hW.bm.integrable (prodMeasure (haarG SU2))
  have i2 := hW'.bm.integrable (prodMeasure (haarG SU2))
  exact relClose_normalize (prodMeasure (haarG SU2)) (fun σ => hW.pos σ) (fun σ => hW'.pos σ) i1 i2 hZ h1 h2

/-- **Lemma T(a) on the real objects:** the images of the SU(2) Wilson measures at `β, β'` under any measurable
blocking (e.g. `(P : RPBlocking SU2 4 N M).B`) are `4|β − β'| · #plaquettes`-relatively close. -/
theorem relClose_wilson_blocked {Y : Type*} [MeasurableSpace Y] (β β' : ℝ) {Φ : GaugeConnection SU2 4 N → Y}
    (hΦ : Measurable Φ) :
    RelClose (2 * (2 * |β - β'| * (univ : Finset (LatticePlaquette 4 N)).card))
      ((wilsonMeasure SU2 2 β 4 N).map Φ) ((wilsonMeasure SU2 2 β' 4 N).map Φ) :=
  (relClose_wilsonMeasure β β').map hΦ

/-- **Lemma T(b) on the real objects:** the block specifications of the SU(2) Wilson measure (conditional law of the
links of `B` given all other links) at `β` and `β'` are `4|β − β'| · #(plaquettes touching B)`-relatively close at
**every** boundary configuration `U`. Local: only the plaquettes touching `B` enter. -/
theorem relClose_wilson_gaugeSpec (β β' : ℝ) (B : Finset (LatticeLink 4 N)) (U : GaugeConnection SU2 4 N) :
    RelClose (2 * (2 * |β - β'| * (touching B).card))
      (gaugeSpec (d := 4) (N := N) (G := SU2) 2 (wilsonWeight β) B U)
      (gaugeSpec (d := 4) (N := N) (G := SU2) 2 (wilsonWeight β') B U) :=
  relClose_locSpec (haarG SU2) (localWeight_wilson β (touching B)) (localWeight_wilson β' (touching B))
    (fun σ => wilson_ratio_le β β' _ σ)
    (fun σ => by have := wilson_ratio_le β' β (touching B) σ; rwa [abs_sub_comm] at this) B U

end Wilson

end ProofPhase.Quantum
