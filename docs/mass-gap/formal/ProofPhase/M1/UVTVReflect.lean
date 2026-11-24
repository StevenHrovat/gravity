/-
Proof phase, M1 tools (m1-tools), Lean phase, module 6: reflection-positive data from a measure, and the reflection
step in `Q(F - f_ℓ)` (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/LEAN-UVTV.md`, `PACK-OSDATA.md`.
-/

import ProofPhase.M1.UVTVOS

/-!
# Reflection-positive data from a measure

**The reflection step** (`condExp_comp_of_measurePreserving`, `os_split_reflection`). For a measure-preserving map
`θ`: `E[F | 𝓗] ∘ θ = E[F ∘ θ | θ⁻¹𝓗]`. Hence the OS norm of `F - E[F | 𝓗]` is the left side of `os_cross_le`, with
`a = F ∘ θ`, `𝓗_a = θ⁻¹𝓗`, `b = F`. So it is bounded by `E|ccov 𝓕 (F ∘ θ) F| + 2 E|E[F ∘ θ | 𝓕] - E[F ∘ θ | θ⁻¹𝓗]|`,
the (B) term plus twice the (A) term, for any `𝓕` containing `𝓗` and `θ⁻¹𝓗`.

**`RPData` from a measure** (`RPData.ofMeasure`). Data:
* a probability space `(Ω, μ)`;
* a measure-preserving involution `θ` (time reflection);
* a measure-preserving shift `s` (time translation by one step) with `s ∘ θ ∘ s = θ`;
* a class `Pos` of positive-time observables, closed under sums, scalar multiples and `· ∘ s`.

Hypotheses (the physics):
* reflection positivity `∫ (u ∘ θ) u dμ ≥ 0`;
* half-step reflection positivity `∫ (u ∘ θ) (u ∘ s) dμ ≥ 0`;

both for bounded measurable `u ∈ Pos`. Then:
* `V` is the bounded measurable functions in `Pos`;
* `Q u v = ∫ (u ∘ θ) v dμ`;
* `τ u = u ∘ s`.

`gap_of_measure` restates `gap_of_RP` for this data. For the Wilson measure on a **finite periodic** lattice, the
repository proves both reflection positivities (`Positivity.wilson_rp`, `Positivity.wilson_rp_link`). But the shift
does not preserve positive-time observables on a torus, so `RPData.ofMeasure` applies to the infinite-time limit (or
the continuum limit). Its hypotheses are what that limit must inherit (`PACK-OSDATA.md`).
-/

open MeasureTheory Finset Filter Topology

open scoped RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.M1.UVTV

/-! ### Conditional expectation under a measure-preserving map -/

section Comp

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Conditional expectation commutes with a measure-preserving map**: `E[F | 𝓗] ∘ θ = E[F ∘ θ | θ⁻¹𝓗]` a.e. -/
theorem condExp_comp_of_measurePreserving {θ : Ω → Ω} (hθ : MeasurePreserving θ μ μ) (𝓗s : ℕ → MeasurableSpace Ω)
    (k : ℕ) (hH : 𝓗s k ≤ m0) {F : Ω → ℝ} (hF : Integrable F μ) :
    (μ[F|𝓗s k]) ∘ θ =ᵐ[μ] μ[F ∘ θ|(𝓗s k).comap θ] := by
  have hθm := hθ.measurable
  have hle : (𝓗s k).comap θ ≤ m0 := (MeasurableSpace.comap_mono hH).trans hθm.comap_le
  have hFθ := hθ.integrable_comp_of_integrable hF
  refine ae_eq_condExp_of_forall_setIntegral_eq hle hFθ ?_ ?_ ?_
  · intro s _ _
    exact (hθ.integrable_comp_of_integrable integrable_condExp).integrableOn
  · intro s hs _
    obtain ⟨t, ht, rfl⟩ := hs
    have htm : MeasurableSet[m0] t := hH t ht
    have e1 : ∫ x in θ ⁻¹' t, (μ[F|𝓗s k] ∘ θ) x ∂μ = ∫ y in t, μ[F|𝓗s k] y ∂μ := by
      have h := setIntegral_map (μ := μ) htm (g := θ) (f := μ[F|𝓗s k])
        (by rw [hθ.map_eq]; exact integrable_condExp.aestronglyMeasurable) hθm.aemeasurable
      rw [hθ.map_eq] at h
      exact h.symm
    have e2 : ∫ x in θ ⁻¹' t, (F ∘ θ) x ∂μ = ∫ y in t, F y ∂μ := by
      have h := setIntegral_map (μ := μ) htm (g := θ) (f := F)
        (by rw [hθ.map_eq]; exact hF.aestronglyMeasurable) hθm.aemeasurable
      rw [hθ.map_eq] at h
      exact h.symm
    rw [e1, e2, setIntegral_condExp hH hF ht]
  · exact (stronglyMeasurable_condExp.comp_measurable (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

/-- **The reflection step in `Q(F - f_ℓ)`**: with `f = E[F | 𝓗]`, for any `𝓕` containing `𝓗` and `θ⁻¹𝓗`,
`|∫ (F∘θ - f∘θ)(F - f) dμ| ≤ E|ccov 𝓕 (F∘θ) F| + 2 E|E[F∘θ | 𝓕] - E[F∘θ | θ⁻¹𝓗]|`. -/
theorem os_split_reflection {θ : Ω → Ω} (hθ : MeasurePreserving θ μ μ) (𝓕s 𝓗s : ℕ → MeasurableSpace Ω) (k : ℕ)
    (hF𝓕 : 𝓕s k ≤ m0) (hH : 𝓗s k ≤ m0) (hH𝓕 : 𝓗s k ≤ 𝓕s k) (hθH : (𝓗s k).comap θ ≤ 𝓕s k) {F : Ω → ℝ}
    (hFm : AEStronglyMeasurable[m0] F μ) (hFb : Bdd1 μ F) :
    |∫ ω, (F (θ ω) - μ[F|𝓗s k] (θ ω)) * (F ω - μ[F|𝓗s k] ω) ∂μ| ≤
      ∫ ω, |ccov μ (𝓕s k) (F ∘ θ) F ω| ∂μ + 2 * ∫ ω, |μ[F ∘ θ|𝓕s k] ω - μ[F ∘ θ|(𝓗s k).comap θ] ω| ∂μ := by
  have hFi : Integrable F μ := hFb.integrable hFm
  have hc := condExp_comp_of_measurePreserving hθ 𝓗s k hH hFi
  have hFθm : AEStronglyMeasurable[m0] (F ∘ θ) μ := (hθ.integrable_comp_of_integrable hFi).aestronglyMeasurable
  have hFθb : Bdd1 μ (F ∘ θ) := hθ.quasiMeasurePreserving.ae hFb
  have key := os_cross_le hF𝓕 hθH hH𝓕 hFθm hFm hFθb hFb
  have hEq : ∫ ω, (F (θ ω) - μ[F|𝓗s k] (θ ω)) * (F ω - μ[F|𝓗s k] ω) ∂μ =
      ∫ ω, ((F ∘ θ) ω - μ[F ∘ θ|(𝓗s k).comap θ] ω) * (F ω - μ[F|𝓗s k] ω) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hc] with ω h
    simp only [Function.comp_apply] at h ⊢
    rw [h]
  rw [hEq]
  exact key

end Comp

/-! ### Reflection-positive data from a measure -/

section Measure

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **A reflection-positive shift-invariant measure** with a class of positive-time observables. -/
structure RPMeasure (μ : Measure Ω) where
  θ : Ω → Ω
  s : Ω → Ω
  θ_mp : MeasurePreserving θ μ μ
  s_mp : MeasurePreserving s μ μ
  θ_invol : ∀ ω, θ (θ ω) = ω
  /-- `θ s θ = s⁻¹`, written without the inverse. -/
  s_θ_s : ∀ ω, s (θ (s ω)) = θ ω
  /-- The positive-time observables. -/
  Pos : (Ω → ℝ) → Prop
  pos_zero : Pos 0
  pos_add : ∀ u v, Pos u → Pos v → Pos (u + v)
  pos_smul : ∀ (c : ℝ) u, Pos u → Pos (c • u)
  pos_shift : ∀ u, Pos u → Pos (u ∘ s)
  /-- Reflection positivity. -/
  rp : ∀ u, Pos u → Measurable u → (∃ C, ∀ ω, |u ω| ≤ C) → 0 ≤ ∫ ω, u (θ ω) * u ω ∂μ
  /-- Reflection positivity through the plane at half a step. -/
  rp_half : ∀ u, Pos u → Measurable u → (∃ C, ∀ ω, |u ω| ≤ C) → 0 ≤ ∫ ω, u (θ ω) * u (s ω) ∂μ

namespace RPMeasure

variable {μ} (M : RPMeasure μ)

/-- The observables: bounded measurable positive-time functions. -/
def Obs : Submodule ℝ (Ω → ℝ) where
  carrier := {u | M.Pos u ∧ Measurable u ∧ ∃ C, ∀ ω, |u ω| ≤ C}
  zero_mem' := ⟨M.pos_zero, measurable_const, 0, fun ω => by simp⟩
  add_mem' := by
    rintro u v ⟨hu, mu, Cu, hCu⟩ ⟨hv, mv, Cv, hCv⟩
    exact ⟨M.pos_add u v hu hv, mu.add mv, Cu + Cv, fun ω =>
      (abs_add_le _ _).trans (add_le_add (hCu ω) (hCv ω))⟩
  smul_mem' := by
    rintro c u ⟨hu, mu, C, hC⟩
    refine ⟨M.pos_smul c u hu, mu.const_smul c, |c| * C, fun ω => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg c)

theorem integrable_mul {u v : Ω → ℝ} (hu : u ∈ M.Obs) (hv : v ∈ M.Obs) {f g : Ω → Ω} (hf : Measurable f)
    (hg : Measurable g) : Integrable (fun ω => u (f ω) * v (g ω)) μ := by
  obtain ⟨-, mu, Cu, hCu⟩ := hu
  obtain ⟨-, mv, Cv, hCv⟩ := hv
  refine Integrable.of_bound (C := Cu * Cv) ((mu.comp hf).mul (mv.comp hg)).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hCu _) (hCv _) (abs_nonneg _) ((abs_nonneg _).trans (hCu (f ω)))

/-- The OS form `Q u v = ∫ (u ∘ θ) v dμ`. -/
def Q : M.Obs →ₗ[ℝ] M.Obs →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ∫ ω, (u : Ω → ℝ) (M.θ ω) * (v : Ω → ℝ) ω ∂μ)
    (fun u₁ u₂ v => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact integral_add (M.integrable_mul u₁.2 v.2 M.θ_mp.measurable measurable_id)
        (M.integrable_mul u₂.2 v.2 M.θ_mp.measurable measurable_id))
    (fun c u v => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul c _)
    (fun u v₁ v₂ => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (M.integrable_mul u.2 v₁.2 M.θ_mp.measurable measurable_id)
        (M.integrable_mul u.2 v₂.2 M.θ_mp.measurable measurable_id))
    (fun c u v => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
      exact integral_const_mul c _)

theorem Q_apply (u v : M.Obs) : M.Q u v = ∫ ω, (u : Ω → ℝ) (M.θ ω) * (v : Ω → ℝ) ω ∂μ := rfl

/-- Substituting `ω ↦ θ ω` (measure preserving). -/
theorem integral_comp_θ (h : Ω → ℝ) : ∫ ω, h (M.θ ω) ∂μ = ∫ ω, h ω ∂μ := by
  have e : MeasurableEmbedding M.θ :=
    (MeasurableEquiv.mk ⟨M.θ, M.θ, M.θ_invol, M.θ_invol⟩ M.θ_mp.measurable M.θ_mp.measurable).measurableEmbedding
  exact M.θ_mp.integral_comp e h

/-- Substituting `ω ↦ s ω` (measure preserving); `s` need not be injective here, so integrability is assumed. -/
theorem integral_comp_s {h : Ω → ℝ} (hh : AEStronglyMeasurable h μ) : ∫ ω, h (M.s ω) ∂μ = ∫ ω, h ω ∂μ := by
  rw [← integral_map M.s_mp.measurable.aemeasurable (by rwa [M.s_mp.map_eq]), M.s_mp.map_eq]

theorem Q_symm (u v : M.Obs) : M.Q u v = M.Q v u := by
  rw [Q_apply, Q_apply, ← M.integral_comp_θ]
  simp only [M.θ_invol]
  exact integral_congr_ae (ae_of_all _ fun ω => mul_comm _ _)

/-- The time translation on observables. -/
def τ : M.Obs →ₗ[ℝ] M.Obs where
  toFun u := ⟨(u : Ω → ℝ) ∘ M.s, M.pos_shift _ u.2.1, u.2.2.1.comp M.s_mp.measurable,
    u.2.2.2.choose, fun ω => u.2.2.2.choose_spec (M.s ω)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem τ_coe (u : M.Obs) : ((M.τ u : M.Obs) : Ω → ℝ) = (u : Ω → ℝ) ∘ M.s := rfl

theorem τ_symm (u v : M.Obs) : M.Q (M.τ u) v = M.Q u (M.τ v) := by
  rw [Q_apply, Q_apply, τ_coe, τ_coe]
  simp only [Function.comp_apply]
  have hm : AEStronglyMeasurable (fun ω => (u : Ω → ℝ) (M.s (M.θ ω)) * (v : Ω → ℝ) ω) μ :=
    (M.integrable_mul u.2 v.2 (M.s_mp.measurable.comp M.θ_mp.measurable) measurable_id).aestronglyMeasurable
  rw [← M.integral_comp_s hm]
  simp only [Function.comp_apply, M.s_θ_s]

theorem τ_pos (u : M.Obs) : 0 ≤ M.Q u (M.τ u) := by
  rw [Q_apply, τ_coe]
  exact M.rp_half _ u.2.1 u.2.2.1 u.2.2.2

theorem τ_pow_coe (u : M.Obs) (k : ℕ) : (((M.τ ^ k) u : M.Obs) : Ω → ℝ) = (u : Ω → ℝ) ∘ M.s^[k] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, τ_coe, ih, Function.iterate_succ, Function.comp_assoc]

/-- **`RPData` from a reflection-positive shift-invariant measure.** -/
def toRPData : RPData M.Obs where
  Q := M.Q
  symm := M.Q_symm
  pos u := M.rp _ u.2.1 u.2.2.1 u.2.2.2
  τ := M.τ
  τ_symm := M.τ_symm
  τ_pos := M.τ_pos
  bdd u := by
    obtain ⟨C, hC⟩ := u.2.2.2
    refine ⟨C * C, fun k => ?_⟩
    show M.Q ((M.τ ^ k) u) ((M.τ ^ k) u) ≤ C * C
    set w := (M.τ ^ k) u with hwdef
    have hw : ∀ ω, |(w : Ω → ℝ) ω| ≤ C := fun ω => by
      rw [hwdef, τ_pow_coe, Function.comp_apply]; exact hC _
    have hb : ∀ ω, |(w : Ω → ℝ) (M.θ ω) * (w : Ω → ℝ) ω| ≤ C * C := fun ω => by
      rw [abs_mul]; exact mul_le_mul (hw _) (hw _) (abs_nonneg _) ((abs_nonneg _).trans (hw (M.θ ω)))
    have hint := M.integrable_mul w.2 w.2 M.θ_mp.measurable measurable_id
    calc M.Q w w = ∫ ω, (w : Ω → ℝ) (M.θ ω) * (w : Ω → ℝ) ω ∂μ := rfl
      _ ≤ ∫ ω, |(w : Ω → ℝ) (M.θ ω) * (w : Ω → ℝ) ω| ∂μ := integral_mono hint hint.abs fun ω => le_abs_self _
      _ ≤ ∫ _ω, C * C ∂μ := integral_mono hint.abs (integrable_const _) hb
      _ = C * C := by simp

/-- **The gap for local observables, at the level of the measure** (`gap_of_RP` for `toRPData`, with Lemma UV-TV's
split through the reflection step `os_split_reflection`). The block approximants are `f_k = E[F | 𝓗_k]`; the inputs are
* `hdec`: the block-level gap;
* `hB`: (B), `E|ccov 𝓕_k (F∘θ) F| ≤ b_B k`;
* `hA`: (A), `E|E[F∘θ | 𝓕_k] - E[F∘θ | θ⁻¹𝓗_k]| ≤ b_A k`;

with `b_A, b_B → 0`. Then `∫ F(θω) F(sⁿω) dμ ≤ e^{-mn} ∫ F(θω) F(ω) dμ`. -/
theorem gap_of_measure (Blk : Submodule ℝ M.Obs) (hτ : ∀ g ∈ Blk, M.τ g ∈ Blk) (m : ℝ)
    (hdec : ∀ g ∈ Blk, ∃ C : ℝ, ∀ n : ℕ, M.Q g ((M.τ ^ n) g) ≤ C * Real.exp (-(m * n)))
    (F : M.Obs) (hF1 : Bdd1 μ (F : Ω → ℝ))
    (𝓕 𝓗 : ℕ → MeasurableSpace Ω) (hF𝓕 : ∀ k, 𝓕 k ≤ ‹MeasurableSpace Ω›) (hH : ∀ k, 𝓗 k ≤ ‹MeasurableSpace Ω›)
    (hH𝓕 : ∀ k, 𝓗 k ≤ 𝓕 k) (hθH : ∀ k, (𝓗 k).comap M.θ ≤ 𝓕 k)
    (f : ℕ → M.Obs) (hf : ∀ k, f k ∈ Blk) (hfE : ∀ k, (f k : Ω → ℝ) = μ[(F : Ω → ℝ)|𝓗 k])
    (bA bB : ℕ → ℝ)
    (hB : ∀ k, ∫ ω, |ccov μ (𝓕 k) ((F : Ω → ℝ) ∘ M.θ) F ω| ∂μ ≤ bB k)
    (hA : ∀ k, ∫ ω, |μ[(F : Ω → ℝ) ∘ M.θ|𝓕 k] ω - μ[(F : Ω → ℝ) ∘ M.θ|(𝓗 k).comap M.θ] ω| ∂μ ≤ bA k)
    (hlimA : Tendsto bA atTop (𝓝 0)) (hlimB : Tendsto bB atTop (𝓝 0)) (n : ℕ) :
    M.Q F ((M.τ ^ n) F) ≤ Real.exp (-(m * n)) * M.Q F F := by
  refine M.toRPData.gap_of_RP Blk hτ m hdec F f hf bA bB (fun k => ?_) hlimA hlimB n
  have hsplit := os_split_reflection M.θ_mp 𝓕 𝓗 k (hF𝓕 k) (hH k) (hH𝓕 k) (hθH k) F.2.2.1.aestronglyMeasurable hF1
  have hQ : M.Q (F - f k) (F - f k) =
      ∫ ω, ((F : Ω → ℝ) (M.θ ω) - μ[(F : Ω → ℝ)|𝓗 k] (M.θ ω)) * ((F : Ω → ℝ) ω - μ[(F : Ω → ℝ)|𝓗 k] ω) ∂μ := by
    rw [Q_apply, Submodule.coe_sub, hfE k]
    rfl
  change M.Q (F - f k) (F - f k) ≤ bB k + 2 * bA k
  rw [hQ]
  exact (le_abs_self _).trans (hsplit.trans (add_le_add (hB k) (by linarith [hA k])))

end RPMeasure

end Measure

end ProofPhase.M1.UVTV
