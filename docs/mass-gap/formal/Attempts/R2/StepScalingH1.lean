/-
Attempt round 2 (2026-11-21), attempt D: (H1) from a step-scaling line of constant physics. Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/r2-stepscaling/NOTE.md` (sections 1, 4 and 5).
-/

import Attempts.R2.StepScaling
import OneScale.Effective.Physical

/-!
# (H1) `EffectiveConvergence` from a coupling-defined scale and control by one number

**Setting.** Levels `k` (bare lattice theories, e.g. Wilson at `β_k`). At level `k`, `u k j` is an inverse coupling of
a box of side `ℓ₀ 2^j` lattice units, defined from the box (Schroedinger-functional type: the box's free-energy response
to a boundary rotation, normalised to the bare inverse coupling at tree level; follow-up experiment 1). Any
normalisation: `1/g²`, `β`, or `1/α_s = 4π/g²` (`Attempts.R2.phi_rescale`). `Jk k` is the **scale-setting layer**: the
block side `ℓ₀ 2^{J_k}` is declared to be the physical length `L₁`, so `a_k = L₁/(ℓ₀ 2^{J_k})`. `P v k` is the block
specification of the effective theory at that block side.

**Hypotheses.**
* (UV) `u k 0 → ∞`: the bare coupling goes to zero (the weak-coupling end, where perturbative input lives).
* (Run) `u k j - u k (j+1) ≤ C`: the coupling runs at most a bounded amount per doubling (implied by the step-scaling
  recursion with bounded remainder).
* (Tune) `u k (J_k) → u*`: **line of constant physics**: at the scale-setting layer the coupling equals a fixed `O(1)`
  value `u*` (in `α_s` language: `α_s(L₁) = α*`, `L₁` is where `α_s` reaches the hand-over value).
* (Ctrl) **control by one number**: there are reference block specifications `Q u` (one family per value of the
  coupling) such that the effective specification at layer `J` with coupling `w` is within `η(J)` of `Q w` in
  `SpecDist`, with lattice artefacts `η(J) → 0` as the block side in lattice units grows.
* (Cont) `Q` is continuous at `u*` in `SpecDist` (modulus `ω`).
* blocks fixed in coarse units and finite range (items 1, 2 of `EffectiveConvergence`).

**Results.**
* `layers_tendsto`: (UV), (Run), (Tune) give `J_k → ∞`, hence `a_k → 0` (`spacing_tendsto`), and the blocks have
  physical size exactly `L₁` (`blockSize_eq`).
* **`effectiveConvergence_of_stepScaling`**: (Tune), (Ctrl), (Cont) and `J_k → ∞` give `EffectiveConvergence` with limit
  `Q u*` and `δ_k = ω(u_k(J_k) - u*) + η(J_k)`.
* **`gap_of_stepScaling`**: with (H2) `LimitGDS` for `Q u*`, the physical gap of `gap_of_effective`.
* `photon_no_line`: for a coupling that does not run (`u_j - u_{j+1} ≤ η_j`, `∑ η ≤ H`: U(1), no running or screening),
  (UV) and (Tune) are incompatible: the theorem is empty for the photon.

**What carries the weight.** Only (Ctrl) at `u*` is non-perturbative and non-trivial: as a hypothesis it is stronger than
(H1) itself (it is (H1) for every value of the coupling, uniformly in the bare coupling). The step-scaling recursion
enters only through `J_k → ∞` (bounded running) and, with its exact one- and two-loop coefficients, through
**asymptotic scaling** of the line of constant physics (`Attempts.R2.scaling_window`, `scaling_drift`), which the gap in
units of `L₁` does not need. See the note, section 4, for the split of (Ctrl) into a weak-coupling part and an
elementary transport.
-/

open MeasureTheory Finset Filter Topology
open OneScale OneScale.Effective

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.R2

/-! ## The dual distance is a pseudometric -/

/-- Triangle inequality for `SpecDist`. -/
theorem specDist_trans {ι S : Type*} [DecidableEq ι] [MeasurableSpace S] {B : Finset ι}
    {q q' q'' : (ι → S) → Measure (ι → S)} {δ δ' : ℝ} (h1 : SpecDist B q q' δ) (h2 : SpecDist B q' q'' δ') :
    SpecDist B q q'' (δ + δ') := by
  intro σ F L hF hFB hL
  have a := h1 σ F L hF hFB hL
  have b := h2 σ F L hF hFB hL
  calc |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q'' σ)|
      ≤ |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q' σ)| + |∫ ξ, F ξ ∂(q' σ) - ∫ ξ, F ξ ∂(q'' σ)| := abs_sub_le _ _ _
    _ ≤ δ * L + δ' * L := add_le_add a b
    _ = (δ + δ') * L := by ring

/-! ## The scale-setting layer goes to infinity -/

/-- Bounded running: `u₀ - u_n ≤ C n`. -/
theorem drop_le (u : ℕ → ℝ) {C : ℝ} (h : ∀ j, u j - u (j + 1) ≤ C) (n : ℕ) : u 0 - u n ≤ C * n := by
  induction n with
  | zero => simp
  | succ n ih => push_cast; linarith [h n]

/-- **The scale-setting layer goes to infinity.** (UV) `u_k(0) → ∞`, (Run) at most `C` per doubling, and (Tune)
`u_k(J_k) → u*` give `J_k → ∞`: the block side `ℓ₀ 2^{J_k}` in lattice units grows without bound. -/
theorem layers_tendsto (u : ℕ → ℕ → ℝ) (Jk : ℕ → ℕ) {C ustar : ℝ} (hC : 0 < C)
    (hUV : Tendsto (fun k => u k 0) atTop atTop) (hrun : ∀ k j, u k j - u k (j + 1) ≤ C)
    (htune : Tendsto (fun k => u k (Jk k)) atTop (𝓝 ustar)) : Tendsto Jk atTop atTop := by
  refine (tendsto_natCast_atTop_iff (R := ℝ)).1 ?_
  have hlow : Tendsto (fun k => (u k 0 - (ustar + 1)) / C) atTop atTop :=
    (tendsto_atTop_add_const_right _ _ hUV).atTop_div_const hC
  refine tendsto_atTop_mono' atTop ?_ hlow
  have hev : ∀ᶠ k in atTop, u k (Jk k) < ustar + 1 := (tendsto_order.1 htune).2 _ (by linarith)
  filter_upwards [hev] with k hk
  rw [div_le_iff₀ hC]
  have := drop_le (u k) (hrun k) (Jk k)
  linarith

/-- The lattice spacing of the line of constant physics, `a_k = L₁/(ℓ₀ 2^{J_k})`. -/
def spacing (L₁ : ℝ) (ℓ₀ : ℕ) (Jk : ℕ → ℕ) (k : ℕ) : ℝ := L₁ / ((ℓ₀ : ℝ) * 2 ^ Jk k)

theorem spacing_pos {L₁ : ℝ} (hL₁ : 0 < L₁) {ℓ₀ : ℕ} (hℓ₀ : 0 < ℓ₀) (Jk : ℕ → ℕ) (k : ℕ) :
    0 < spacing L₁ ℓ₀ Jk k := by
  unfold spacing; have : (0 : ℝ) < ℓ₀ := by exact_mod_cast hℓ₀
  positivity

theorem spacing_tendsto {L₁ : ℝ} {ℓ₀ : ℕ} (hℓ₀ : 0 < ℓ₀) {Jk : ℕ → ℕ} (hJ : Tendsto Jk atTop atTop) :
    Tendsto (spacing L₁ ℓ₀ Jk) atTop (𝓝 0) := by
  have hℓ : (0 : ℝ) < ℓ₀ := by exact_mod_cast hℓ₀
  have h2 : Tendsto (fun k => (2 : ℝ) ^ Jk k) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp hJ
  exact tendsto_const_nhds.div_atTop (h2.const_mul_atTop hℓ)

/-- The blocks of the line of constant physics have physical size exactly `L₁`. -/
theorem blockSize_eq {L₁ : ℝ} (hL₁ : 0 < L₁) {ℓ₀ : ℕ} (hℓ₀ : 0 < ℓ₀) (Jk : ℕ → ℕ) (k : ℕ) :
    blockSize L₁ (spacing L₁ ℓ₀ Jk) k = L₁ := by
  have hℓ : (0 : ℝ) < ℓ₀ := by exact_mod_cast hℓ₀
  have hd : L₁ / spacing L₁ ℓ₀ Jk k = ((ℓ₀ * 2 ^ Jk k : ℕ) : ℝ) := by
    unfold spacing; push_cast; field_simp
  unfold blockSize CorollaryB.side
  rw [hd, Nat.ceil_natCast]
  unfold spacing; push_cast; field_simp

/-! ## The conditional theorem -/

section Main

variable {V : Type*} {ι : V → Type*} [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)] {S : Type*} [MeasurableSpace S]
  {J : V → Type*} [∀ v, Fintype (J v)]

/-- **(H1) from a coupling-defined scale and control by one number.** If at the scale-setting layers the coupling
tends to `u*` (Tune), the layers go to infinity, the effective specifications at those layers are within the artefact
`η(J_k)` of the reference specification `Q(u_k(J_k))` (Ctrl), and `Q` is continuous at `u*` (Cont), then
`EffectiveConvergence` holds with limit `Q u*` and `δ_k = ω(u_k(J_k) - u*) + η(J_k)`. -/
theorem effectiveConvergence_of_stepScaling {μ : ∀ v, ℕ → Measure (ι v → S)} (P : ∀ v k, BlockSpec (μ v k) (J v))
    (block shell : ∀ v, J v → Finset (ι v)) (u : ℕ → ℕ → ℝ) (Jk : ℕ → ℕ) {ustar : ℝ}
    (hJ : Tendsto Jk atTop atTop) (htune : Tendsto (fun k => u k (Jk k)) atTop (𝓝 ustar))
    (hblock : ∀ v k, (P v k).block = block v) (hloc : ∀ v k j, IsLocal (shell v j) ((P v k).spec j))
    (Q : ℝ → ∀ v, J v → (ι v → S) → Measure (ι v → S)) (η : ℕ → ℝ) (hη0 : ∀ n, 0 ≤ η n)
    (hη : Tendsto η atTop (𝓝 0))
    (hctrl : ∀ v k j, SpecDist (block v j) (Q (u k (Jk k)) v j) ((P v k).spec j) (η (Jk k)))
    (ω : ℝ → ℝ) (hω0 : ∀ t, 0 ≤ ω t) (hω : Tendsto ω (𝓝 0) (𝓝 0))
    (hcont : ∀ w v j, SpecDist (block v j) (Q ustar v j) (Q w v j) (ω (w - ustar))) :
    EffectiveConvergence P block shell (Q ustar) := by
  refine ⟨hblock, hloc, fun k => ω (u k (Jk k) - ustar) + η (Jk k), fun k => add_nonneg (hω0 _) (hη0 _), ?_, ?_⟩
  · have h1 : Tendsto (fun k => ω (u k (Jk k) - ustar)) atTop (𝓝 0) := by
      refine hω.comp ?_
      have := htune.sub_const ustar
      rwa [sub_self] at this
    simpa using h1.add (hη.comp hJ)
  · intro v k j
    exact specDist_trans (hcont (u k (Jk k)) v j) (hctrl v k j)

/-- **The gap from a step-scaling line of constant physics and (H2).** Under (UV), (Run), (Tune), (Ctrl), (Cont) and
(H2) `LimitGDS` for the limit `Q u*`, with the lattice spacings `a_k = L₁/(ℓ₀ 2^{J_k}) → 0` of the line of constant
physics, block observables of every volume decay at a physical rate `m > 0` (in units of `L₁`, the length where the
coupling equals `u*`), uniformly in `k ≥ k₀` and in the volume. -/
theorem gap_of_stepScaling [∀ v, Nonempty (ι v)] {μ : ∀ v, ℕ → Measure (ι v → S)}
    [∀ v k, IsProbabilityMeasure (μ v k)] (P : ∀ v k, BlockSpec (μ v k) (J v))
    (block shell : ∀ v, J v → Finset (ι v)) (dist : ∀ v, ι v → ι v → ℝ) {cmin cmax b : ℕ} {D₀ D₁ r : ℝ}
    (hD₁ : 0 < D₁) (G : ∀ v, UniformGeometry (block v) (shell v) (dist v) cmin cmax b D₀ D₁ r)
    {L₁ : ℝ} (hL₁ : 0 < L₁) {ℓ₀ : ℕ} (hℓ₀ : 0 < ℓ₀)
    (u : ℕ → ℕ → ℝ) (Jk : ℕ → ℕ) {C ustar : ℝ} (hC : 0 < C)
    (hUV : Tendsto (fun k => u k 0) atTop atTop) (hrun : ∀ k j, u k j - u k (j + 1) ≤ C)
    (htune : Tendsto (fun k => u k (Jk k)) atTop (𝓝 ustar))
    (hblock : ∀ v k, (P v k).block = block v) (hloc : ∀ v k j, IsLocal (shell v j) ((P v k).spec j))
    (Q : ℝ → ∀ v, J v → (ι v → S) → Measure (ι v → S)) (η : ℕ → ℝ) (hη0 : ∀ n, 0 ≤ η n)
    (hη : Tendsto η atTop (𝓝 0))
    (hctrl : ∀ v k j, SpecDist (block v j) (Q (u k (Jk k)) v j) ((P v k).spec j) (η (Jk k)))
    (ω : ℝ → ℝ) (hω0 : ∀ t, 0 ≤ ω t) (hω : Tendsto ω (𝓝 0) (𝓝 0))
    (hcont : ∀ w v j, SpecDist (block v j) (Q ustar v j) (Q w v j) (ω (w - ustar)))
    (hH2 : LimitGDS block (Q ustar)) :
    ∃ m : ℝ, 0 < m ∧ ∃ C' : ℝ, 0 ≤ C' ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ v,
      ∀ (f g : (ι v → S) → ℝ) (A Sg : Finset (ι v)) (vf : ι v → ℝ) (Lg R : ℝ),
        BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) → 0 ≤ R →
        (∀ x ∈ A, ∀ y ∈ Sg, R ≤ L₁ * dist v x y) →
        |∫ σ, f σ * g σ ∂(μ v k) - (∫ σ, f σ ∂(μ v k)) * ∫ σ, g σ ∂(μ v k)| ≤
          C' * (cmax * ∑ x ∈ A, vf x) * Lg * Real.exp (-(m * R)) := by
  have hJ := layers_tendsto u Jk hC hUV hrun htune
  have hH1 := effectiveConvergence_of_stepScaling P block shell u Jk hJ htune hblock hloc Q η hη0 hη hctrl ω hω0
    hω hcont
  obtain ⟨m, hm, C', hC', k₀, h⟩ := gap_of_effective P block shell (Q ustar) dist hD₁ G hL₁
    (spacing_pos hL₁ hℓ₀ Jk) (spacing_tendsto hℓ₀ hJ) ⟨hH1, hH2⟩
  refine ⟨m, hm, C', hC', k₀, fun k hk v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR0 hR => ?_⟩
  refine h k hk v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR0 ?_
  intro x hx y hy
  rw [blockSize_eq hL₁ hℓ₀ Jk k]
  exact hR x hx y hy

end Main

/-! ## Photon test -/

/-- **Photon test.** If at every level the coupling does not run (`u_k(j) - u_k(j+1) ≤ η_j` with `∑ η ≤ H`: U(1),
no running, or screening), then (UV) `u_k(0) → ∞` and (Tune) `u_k(J_k) → u*` cannot both hold: there is no line of
constant physics from weak bare coupling, and `gap_of_stepScaling` says nothing. -/
theorem photon_no_line (u : ℕ → ℕ → ℝ) (Jk : ℕ → ℕ) {H ustar : ℝ} (η : ℕ → ℝ)
    (hrun : ∀ k j, u k j - u k (j + 1) ≤ η j) (hH : ∀ n, ∑ j ∈ range n, η j ≤ H)
    (hUV : Tendsto (fun k => u k 0) atTop atTop) (htune : Tendsto (fun k => u k (Jk k)) atTop (𝓝 ustar)) :
    False := by
  have hev1 : ∀ᶠ k in atTop, ustar + 1 + H < u k 0 := hUV.eventually_gt_atTop _
  have hev2 : ∀ᶠ k in atTop, u k (Jk k) < ustar + 1 := (tendsto_order.1 htune).2 _ (by linarith)
  obtain ⟨k, h1, h2⟩ := (hev1.and hev2).exists
  have := photon_never_reaches (u k) η (hrun k) hH h1 (Jk k)
  linarith

end Attempts.R2
