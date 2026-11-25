/-
Proof phase, M1 tools (m1-tools), Lean phase, module 5: the OS reconstruction from reflection-positive data, which
discharges `OSData` (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/LEAN-UVTV.md`, `PACK-OSDATA.md`.
-/

import ProofPhase.M1.UVTVInterface

/-!
# The OS reconstruction from reflection-positive data

**Data (`RPData`).** A real vector space `V` (the positive-time observables), a bilinear form `Q u v` (`= E[θu · v]`),
symmetric and positive semidefinite (**reflection positivity**), and a linear map `τ` (the time translation by one step)
with
* `Q (τ u) v = Q u (τ v)` (symmetry of the transfer);
* `Q u (τ u) ≥ 0` (positivity of the transfer: reflection positivity through the plane at half a step);
* `Q (τ^k u) (τ^k u) ≤ C_u` for all `k` (bounded observables: `E[θw · w] ≤ ‖w‖_∞²`).

**The construction.**
* `RPData.Pre`: `V` with `Q` as a degenerate inner product (Mathlib's `PreInnerProductSpace.Core`). `RPData.H` is its
  completion (`UniformSpace.Completion`), a real Hilbert space. The null vectors are identified automatically, since
  the completion is Hausdorff.
* `RPData.Φ : V →ₗ H` with `⟪Φ u, Φ v⟫ = Q u v`. So `RPData.osData : OSData V H` with `‖Φ u‖² = Q u u`: **this
  discharges the named hypothesis `OSData`** of `UVTVInterface`.
* `RPData.contraction`: **the OS contraction** `Q (τu) (τu) ≤ Q u u`. The proof uses Cauchy-Schwarz and the
  log-convexity of `k ↦ Q (τ^k u) (τ^k u)` (`Interface.logconvex_ratio`), plus boundedness.
* `RPData.T : H →L H`: the transfer operator, the continuous extension of `τ`, with `T (Φ u) = Φ (τ u)`, symmetric
  (`T_symm`) and positive (`T_pos`).
* `RPData.H0`: for a `τ`-invariant subspace `Blk` of block observables, the closure of `Φ(Blk)`. It is closed,
  `T`-invariant (`T_mem_H0`), contains the block vectors, and lies in their closure.

**The result (`gap_of_RP`).** Everything in terms of `V`, `Q`, `τ`:
* if every block observable `g ∈ Blk` has `Q g (τ^n g) ≤ C_g e^{-mn}` (the block-level gap);
* and `F` has block approximants `f_k ∈ Blk` with `Q(F - f_k, F - f_k) ≤ b_B k + 2 b_A k → 0` (Lemma UV-TV, (B) + 2(A));

then `Q F (τ^n F) ≤ e^{-mn} Q F F` for all `n`. No Hilbert-space hypothesis is left.

**Not here** (`PACK-OSDATA.md`): building `RPData` from the measures, namely
* `V` the bounded measurable positive-time gauge-invariant observables;
* `Q u v = ∫ (u ∘ θ) v dμ`, with reflection positivity of the (lattice or limit) measure;
* `τ` the time translation, with its two RP properties;

and the identification of `Q(F - f_ℓ)` with `os_cross_le`'s left side.
-/

open Filter Topology UniformSpace

open scoped RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.M1.UVTV

/-- **Reflection-positive data** with a transfer step. -/
structure RPData (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The OS form `Q u v = E[θu · v]`. -/
  Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  symm : ∀ u v, Q u v = Q v u
  /-- Reflection positivity. -/
  pos : ∀ u, 0 ≤ Q u u
  /-- The time translation by one step. -/
  τ : V →ₗ[ℝ] V
  τ_symm : ∀ u v, Q (τ u) v = Q u (τ v)
  τ_pos : ∀ u, 0 ≤ Q u (τ u)
  /-- Bounded observables stay bounded under translation. -/
  bdd : ∀ u, ∃ C : ℝ, ∀ k : ℕ, Q ((τ ^ k) u) ((τ ^ k) u) ≤ C

namespace RPData

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (R : RPData V)

/-! ### The contraction -/

theorem pow_succ_apply (u : V) (k : ℕ) : (R.τ ^ (k + 1)) u = R.τ ((R.τ ^ k) u) := by
  rw [pow_succ', Module.End.mul_apply]

/-- Cauchy-Schwarz for the OS form. -/
theorem cauchy_schwarz (x y : V) : R.Q x y * R.Q x y ≤ R.Q x x * R.Q y y := by
  have key : ∀ t : ℝ, 0 ≤ R.Q x x * t ^ 2 + 2 * R.Q x y * t + R.Q y y := by
    intro t
    have h := R.pos (t • x + y)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [R.symm y x] at h
    nlinarith [h]
  by_cases h0 : R.Q x x = 0
  · have hxy : R.Q x y = 0 := by
      by_contra hne
      have ht := key (-(R.Q y y + 1) / (2 * R.Q x y))
      have e : 2 * R.Q x y * (-(R.Q y y + 1) / (2 * R.Q x y)) = -(R.Q y y + 1) := by field_simp
      rw [h0, zero_mul, zero_add, e] at ht
      linarith
    rw [hxy, h0]; simp
  · have hpos : 0 < R.Q x x := lt_of_le_of_ne (R.pos x) (Ne.symm h0)
    have := key (-(R.Q x y) / R.Q x x)
    have e : R.Q x x * (-R.Q x y / R.Q x x) ^ 2 + 2 * R.Q x y * (-R.Q x y / R.Q x x) + R.Q y y =
        R.Q y y - R.Q x y * R.Q x y / R.Q x x := by field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ hpos] at this
    linarith

/-- **The OS contraction**: `Q (τ u) (τ u) ≤ Q u u`. -/
theorem contraction (u : V) : R.Q (R.τ u) (R.τ u) ≤ R.Q u u := by
  set a : ℕ → ℝ := fun k => R.Q ((R.τ ^ k) u) ((R.τ ^ k) u) with ha
  have a0 : a 0 = R.Q u u := by simp [a]
  have a1 : a 1 = R.Q (R.τ u) (R.τ u) := by simp [a]
  -- `a (k+1) = Q (τ^k u) (τ^(k+2) u)`
  have hshift : ∀ k, a (k + 1) = R.Q ((R.τ ^ k) u) ((R.τ ^ (k + 2)) u) := by
    intro k
    simp only [a]
    rw [R.pow_succ_apply, R.τ_symm, ← R.pow_succ_apply, ← R.pow_succ_apply]
  have hlc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2) := by
    intro k
    rw [sq, hshift k]
    exact R.cauchy_schwarz _ _
  have hnn : ∀ k, 0 ≤ a k := fun k => R.pos _
  rw [← a0, ← a1]
  rcases (hnn 1).eq_or_lt with h1 | h1
  · rw [← h1]; exact hnn 0
  rcases (hnn 0).eq_or_lt with h0 | h0
  · -- `a 0 = 0` forces `a 1 = 0`
    have := hlc 0
    rw [← h0, zero_mul] at this
    nlinarith
  -- both positive: geometric growth at rate `a 1 / a 0` unless it is `≤ 1`
  obtain ⟨C, hC⟩ := R.bdd u
  have hgrow : ∀ k, a 0 * (a 1 / a 0) ^ k ≤ a k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h := (ProofPhase.Interface.logconvex_ratio hlc h0 h1 k).2
        have hr : 0 ≤ a 1 / a 0 := (div_pos h1 h0).le
        calc a 0 * (a 1 / a 0) ^ (k + 1) = a 1 / a 0 * (a 0 * (a 1 / a 0) ^ k) := by ring
          _ ≤ a 1 / a 0 * a k := mul_le_mul_of_nonneg_left ih hr
          _ ≤ a (k + 1) := h
  by_contra hlt
  push Not at hlt
  have hr : 1 < a 1 / a 0 := by rw [one_lt_div h0]; exact hlt
  have ht : Tendsto (fun k : ℕ => a 0 * (a 1 / a 0) ^ k) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).const_mul_atTop h0
  obtain ⟨k, hk⟩ := (ht.eventually (eventually_gt_atTop C)).exists
  linarith [hgrow k, hC k]

/-! ### The pre-Hilbert space and its completion -/

/-- `V` with the OS form as a degenerate inner product. -/
def Pre (_R : RPData V) : Type _ := V

instance : AddCommGroup R.Pre := inferInstanceAs (AddCommGroup V)

instance : Module ℝ R.Pre := inferInstanceAs (Module ℝ V)

/-- The identity `V → Pre`, as a linear map. -/
def toPre : V →ₗ[ℝ] R.Pre where
  toFun u := u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Q_smul_left (x y : V) (r : ℝ) : R.Q (r • x) y = (starRingEnd ℝ) r * R.Q x y := by
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, conj_trivial]

instance core : PreInnerProductSpace.Core ℝ R.Pre where
  inner u v := R.Q u v
  conj_inner_symm u v := by
    rw [starRingEnd_apply, star_trivial]
    exact R.symm v u
  re_inner_nonneg u := by simpa using R.pos u
  add_left u v w := (congrArg (fun f => f w) (R.Q.map_add u v)).trans (LinearMap.add_apply (R.Q u) (R.Q v) w)
  smul_left u v r := R.Q_smul_left u v r

instance : SeminormedAddCommGroup R.Pre := InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

instance : InnerProductSpace ℝ R.Pre := InnerProductSpace.ofCore R.core

theorem inner_pre (u v : V) : ⟪(R.toPre u : R.Pre), R.toPre v⟫ = R.Q u v := rfl

/-- The OS Hilbert space. -/
abbrev H : Type _ := Completion R.Pre

/-- The embedding of observables into the OS Hilbert space. -/
def Φ : V →ₗ[ℝ] R.H := (Completion.toComplₗᵢ (𝕜 := ℝ) (E := R.Pre)).toLinearMap.comp R.toPre

theorem Φ_apply (u : V) : R.Φ u = ((R.toPre u : R.Pre) : Completion R.Pre) := rfl

theorem inner_Φ (u v : V) : ⟪R.Φ u, R.Φ v⟫ = R.Q u v := by
  rw [Φ_apply, Φ_apply, Completion.inner_coe]; rfl

theorem norm_sq_Φ (u : V) : ‖R.Φ u‖ ^ 2 = R.Q u u := by
  rw [← real_inner_self_eq_norm_sq, inner_Φ]

/-- **`OSData` discharged**: the OS Hilbert space with `‖Φ u‖² = Q u u`. -/
def osData : OSData V R.H where
  Φ := R.Φ
  Q := fun u => R.Q u u
  norm_sq := R.norm_sq_Φ

/-! ### The transfer operator -/

theorem norm_τ_le (x : R.Pre) : ‖R.toPre (R.τ x)‖ ≤ ‖x‖ := by
  have h1 : ‖R.toPre (R.τ x)‖ ^ 2 = R.Q (R.τ x) (R.τ x) := by
    rw [← real_inner_self_eq_norm_sq]; rfl
  have h2 : ‖x‖ ^ 2 = R.Q x x := by
    rw [← real_inner_self_eq_norm_sq]; rfl
  have h := R.contraction x
  rw [← h1, ← h2] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- `τ` on the pre-Hilbert space, continuous with norm `≤ 1`. -/
def τPre : R.Pre →L[ℝ] R.Pre :=
  LinearMap.mkContinuous
    { toFun := fun x => R.toPre (R.τ x)
      map_add' := fun x y => R.τ.map_add x y
      map_smul' := fun r x => R.τ.map_smul r x } 1
    fun x => by rw [one_mul]; exact R.norm_τ_le x

/-- **The transfer operator**: the continuous extension of `τ` to the OS Hilbert space. -/
def T : R.H →L[ℝ] R.H :=
  ContinuousLinearMap.extend ((Completion.toComplL : R.Pre →L[ℝ] Completion R.Pre).comp R.τPre)
    (Completion.toComplL : R.Pre →L[ℝ] Completion R.Pre)

theorem T_coe (x : R.Pre) : R.T (x : Completion R.Pre) = ((R.τPre x : R.Pre) : Completion R.Pre) := by
  have hd : DenseRange (Completion.toComplL : R.Pre →L[ℝ] Completion R.Pre) := Completion.denseRange_coe
  have hu : IsUniformInducing (Completion.toComplL : R.Pre →L[ℝ] Completion R.Pre) :=
    Completion.isUniformInducing_coe _
  exact ContinuousLinearMap.extend_eq _ hd hu x

theorem T_Φ (u : V) : R.T (R.Φ u) = R.Φ (R.τ u) := R.T_coe _

theorem T_pow_Φ (u : V) (n : ℕ) : (R.T ^ n) (R.Φ u) = R.Φ ((R.τ ^ n) u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ']
      show R.T ((R.T ^ n) (R.Φ u)) = _
      rw [ih, T_Φ, ← R.pow_succ_apply]

/-- `T` is symmetric. -/
theorem T_symm (x y : R.H) : ⟪R.T x, y⟫ = ⟪x, R.T y⟫ := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq ((R.T.continuous.comp continuous_fst).inner continuous_snd)
      (continuous_fst.inner (R.T.continuous.comp continuous_snd))
  · intro a b
    rw [R.T_coe, R.T_coe, Completion.inner_coe, Completion.inner_coe]
    exact R.τ_symm a b

/-- `T` is positive. -/
theorem T_pos (x : R.H) : 0 ≤ ⟪x, R.T x⟫ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_le continuous_const (continuous_id.inner R.T.continuous)
  · intro a
    rw [R.T_coe, Completion.inner_coe]
    exact R.τ_pos a

/-! ### The block closure -/

variable (Blk : Submodule ℝ V)

/-- The closure of the block vectors. -/
def H0 : Submodule ℝ R.H := (Blk.map R.Φ).topologicalClosure

theorem isClosed_H0 : IsClosed (R.H0 Blk : Set R.H) := Submodule.isClosed_topologicalClosure _

theorem image_subset_H0 : R.Φ '' Blk ⊆ R.H0 Blk := by
  intro x hx
  exact Submodule.le_topologicalClosure _ (by simpa [Submodule.mem_map] using hx)

theorem H0_subset_closure : (R.H0 Blk : Set R.H) ⊆ closure (R.Φ '' Blk) := by
  rw [H0, Submodule.topologicalClosure_coe, Submodule.map_coe]

/-- `T` leaves the block closure invariant when `τ` maps block observables to block observables. -/
theorem T_mem_H0 (hτ : ∀ g ∈ Blk, R.τ g ∈ Blk) : ∀ x ∈ R.H0 Blk, R.T x ∈ R.H0 Blk := by
  intro x hx
  have hx' : x ∈ closure (R.Φ '' Blk) := R.H0_subset_closure Blk hx
  have hmaps : Set.MapsTo R.T (R.Φ '' Blk) (R.Φ '' Blk) := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨R.τ g, hτ g hg, (R.T_Φ g).symm⟩
  show R.T x ∈ (R.H0 Blk : Set R.H)
  rw [H0, Submodule.topologicalClosure_coe, Submodule.map_coe]
  exact map_mem_closure R.T.continuous hx' hmaps

/-! ### The gap, in terms of the reflection-positive data only -/

/-- **The gap for local observables from Lemma UV-TV, with the OS reconstruction done** (`gap_of_UVTV` with
`OSData`, `T` and `H0` constructed here). For a `τ`-invariant subspace `Blk` of block observables:
* `hdec`: the block-level gap, `Q g (τ^n g) ≤ C_g e^{-mn}` for every `g ∈ Blk`;
* `hsplit`: Lemma UV-TV, `Q(F - f_k, F - f_k) ≤ b_B k + 2 b_A k` with `b_A, b_B → 0`.

Then `Q F (τ^n F) ≤ e^{-mn} Q F F` for every `n`. -/
theorem gap_of_RP (hτ : ∀ g ∈ Blk, R.τ g ∈ Blk) (m : ℝ)
    (hdec : ∀ g ∈ Blk, ∃ C : ℝ, ∀ n : ℕ, R.Q g ((R.τ ^ n) g) ≤ C * Real.exp (-(m * n)))
    (F : V) (f : ℕ → V) (hf : ∀ k, f k ∈ Blk) (bA bB : ℕ → ℝ)
    (hsplit : ∀ k, R.Q (F - f k) (F - f k) ≤ bB k + 2 * bA k)
    (hA : Tendsto bA atTop (𝓝 0)) (hB : Tendsto bB atTop (𝓝 0)) (n : ℕ) :
    R.Q F ((R.τ ^ n) F) ≤ Real.exp (-(m * n)) * R.Q F F := by
  have hdecH : ∀ G ∈ R.osData.Φ '' (Blk : Set V), ∃ C : ℝ, ∀ n : ℕ,
      ⟪G, (R.T ^ n) G⟫ ≤ C * Real.exp (-(m * n)) := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨C, hC⟩ := hdec g hg
    refine ⟨C, fun n => ?_⟩
    change ⟪R.Φ g, (R.T ^ n) (R.Φ g)⟫ ≤ _
    rw [R.T_pow_Φ, R.inner_Φ]
    exact hC n
  have h := gap_of_UVTV R.osData R.T R.T_symm R.T_pos (Blk : Set V) (R.H0 Blk) (R.isClosed_H0 Blk)
    (R.image_subset_H0 Blk) (R.H0_subset_closure Blk) (R.T_mem_H0 Blk hτ) m hdecH F f hf bA bB hsplit hA hB n
  change ⟪R.Φ F, (R.T ^ n) (R.Φ F)⟫ ≤ Real.exp (-(m * n)) * ‖R.Φ F‖ ^ 2 at h
  rwa [R.T_pow_Φ, R.inner_Φ, R.norm_sq_Φ] at h

end RPData

end ProofPhase.M1.UVTV
