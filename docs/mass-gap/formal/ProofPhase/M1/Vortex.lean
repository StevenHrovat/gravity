/-
Proof phase, M1 tools (m1-tools): the obstruction to the deterministic Lemma D: a centre vortex at a block centre is
reproduced by every gauge-covariant, rotation-equivariant block average (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/NOTE.md`, section 2.4.
-/

import Mathlib

/-!
# Vortex persistence

`c6f-m1scope/ONE-STEP.md` section 3 conjectured **Lemma D**: for a suitable extension of Balaban's average to all
configurations, an arbitrary old large-field core becomes invisible to the block field after `n` steps up to
`π cⁿ`, `c < 1`. This file shows that **no** extension can do that in general.

The configuration: `U = z` (a central involution, `-1` in SU(2)) on the four fine bonds of a coarse site `y` in
directions `±3, ±4`, and `U = 1` elsewhere. A rotation `ρ` about `y` taking `1 → 3, 2 → 4, 3 → -1, 4 → -2` maps `U`
to its gauge transform by `z` at `y`. Hence, for every blocking map `B` that is

* covariant under the gauge transformation by `z` at the coarse site `y` (`hflip`),
* covariant under global conjugation (`hconj`),
* equivariant under the rotation about `y` (`hrot`; Balaban's contour family is rotation symmetric, [I] p. 252),

the image `B U` is again central-valued and satisfies the same relation `B U ∘ ρ = flip_z (B U)` on the coarse
star (**`vortex_step`**). By induction the `n`-fold block field keeps it at every scale at which `y` is a site
(**`blockTower_vortex`**), and with locality (coarse bonds away from `y` read no bond of the star of `y`, and trivial
input gives trivial output) the coarse plaquettes at `y` in the mixed planes have holonomy `z⁻¹ ≠ 1` at every scale
(**`vortex_plaquette`**). For SU(2): `z = -1`, plaquette value `-1`, i.e. maximal (`su2_negOne_central`,
`su2_negOne_ne_one`).

**Claim level.** Proved, for any group with a central element `z` (the locality and covariance properties are named
hypotheses; that Balaban's bond average [I] (0.4) has them is the paper statement of `NOTE.md` 2.4, with
`log(-1) := 0`; for a non-covariant choice of `log(-1)` the same configuration still gives plaquette `-1`, checked by
hand there).
-/

noncomputable section

namespace ProofPhase.M1

open Classical

variable {G : Type*} [Group G]

/-- Gauge transformation by a central element `z` at one site: multiply every bond of the star `S` by `z`. -/
def flipOn {ι : Type*} (z : G) (S : Set ι) (U : ι → G) : ι → G := fun b => if b ∈ S then z * U b else U b

/-- **One step.** A conjugation-invariant (central-valued) configuration that the rotation maps to its `z`-gauge
transform is mapped by any covariant, equivariant blocking to a configuration with the same two properties. -/
theorem vortex_step {ι κ : Type*} (B : (ι → G) → (κ → G)) (z : G) (Sf : Set ι) (Sc : Set κ) (ρf : ι → ι)
    (ρc : κ → κ) (hconj : ∀ (v : G) (U : ι → G), B (fun b => v * U b * v⁻¹) = fun c => v * B U c * v⁻¹)
    (hflip : ∀ U, B (flipOn z Sf U) = flipOn z Sc (B U)) (hrot : ∀ U, B (U ∘ ρf) = B U ∘ ρc)
    (U : ι → G) (hUc : ∀ b (g : G), g * U b = U b * g) (hUr : U ∘ ρf = flipOn z Sf U) :
    (∀ c (g : G), g * B U c = B U c * g) ∧ B U ∘ ρc = flipOn z Sc (B U) := by
  refine ⟨fun c g => ?_, ?_⟩
  · have hU : (fun b => g * U b * g⁻¹) = U := by
      funext b; rw [hUc b g, mul_assoc, mul_inv_cancel, mul_one]
    have h := congrFun (hconj g U) c
    rw [hU] at h
    -- h : B U c = g * B U c * g⁻¹
    calc g * B U c = g * B U c * g⁻¹ * g := by group
      _ = B U c * g := by rw [← h]
  · rw [← hrot, hUr, hflip]

/-- The blocked tower, explicitly: `blockTower B U₀ n` is the `n`-fold block field. -/
def blockTower (ι : ℕ → Type*) (B : ∀ n, (ι n → G) → (ι (n + 1) → G)) (U₀ : ι 0 → G) : ∀ n, ι n → G
  | 0 => U₀
  | n + 1 => B n (blockTower ι B U₀ n)

/-- **The tower keeps the vortex**, and stays trivial off the star if the blocking is local. -/
theorem blockTower_vortex (ι : ℕ → Type*) (B : ∀ n, (ι n → G) → (ι (n + 1) → G)) (z : G) (S : ∀ n, Set (ι n))
    (ρ : ∀ n, ι n → ι n)
    (hconj : ∀ n (v : G) (U : ι n → G), B n (fun b => v * U b * v⁻¹) = fun c => v * B n U c * v⁻¹)
    (hflip : ∀ n U, B n (flipOn z (S n) U) = flipOn z (S (n + 1)) (B n U))
    (hrot : ∀ n U, B n (U ∘ ρ n) = B n U ∘ ρ (n + 1))
    (U₀ : ι 0 → G) (hUc : ∀ b (g : G), g * U₀ b = U₀ b * g) (hUr : U₀ ∘ ρ 0 = flipOn z (S 0) U₀) (n : ℕ) :
    (∀ b (g : G), g * blockTower ι B U₀ n b = blockTower ι B U₀ n b * g) ∧
      blockTower ι B U₀ n ∘ ρ n = flipOn z (S n) (blockTower ι B U₀ n) := by
  induction n with
  | zero => exact ⟨hUc, hUr⟩
  | succ n ih =>
    exact vortex_step (B n) z (S n) (S (n + 1)) (ρ n) (ρ (n + 1)) (hconj n) (hflip n) (hrot n) _ ih.1 ih.2

/-- Locality: if each coarse bond off the star reads only fine bonds off the star, and trivial input gives trivial
output, the tower is trivial off the star at every scale. -/
theorem blockTower_trivial_off (ι : ℕ → Type*) (B : ∀ n, (ι n → G) → (ι (n + 1) → G)) (S : ∀ n, Set (ι n))
    (read : ∀ n, ι (n + 1) → Set (ι n))
    (hloc : ∀ n (U : ι n → G) c, (∀ b ∈ read n c, U b = 1) → B n U c = 1)
    (hread : ∀ n c, c ∉ S (n + 1) → ∀ b ∈ read n c, b ∉ S n)
    (U₀ : ι 0 → G) (h₀ : ∀ b, b ∉ S 0 → U₀ b = 1) (n : ℕ) :
    ∀ b, b ∉ S n → blockTower ι B U₀ n b = 1 := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    intro c hc
    exact hloc n _ c (fun b hb => ih b (hread n c hc b hb))

/-- **The coarse plaquette at the vortex.** If `c ∈ S` and `ρ c` (both bonds out of the site) carry the vortex
relation and the two far sides of the plaquette are trivial, the plaquette holonomy is `z⁻¹`. -/
theorem vortex_plaquette {ι : Type*} (z : G) (S : Set ι) (ρ : ι → ι) (U : ι → G) (hr : U ∘ ρ = flipOn z S U)
    {c c₂ c₃ : ι} (hc : c ∈ S) (h₂ : U c₂ = 1) (h₃ : U c₃ = 1) :
    U c * U c₂ * (U c₃)⁻¹ * (U (ρ c))⁻¹ = z⁻¹ := by
  have h : U (ρ c) = z * U c := by
    have := congrFun hr c
    simpa [flipOn, hc] using this
  rw [h₂, h₃, h]; group

/-- **Every scale, SU(2)-style:** under the hypotheses of `blockTower_vortex` and `blockTower_trivial_off`, at every
scale `n` the coarse plaquette at the vortex site has holonomy `z⁻¹`. -/
theorem vortex_persists (ι : ℕ → Type*) (B : ∀ n, (ι n → G) → (ι (n + 1) → G)) (z : G) (S : ∀ n, Set (ι n))
    (ρ : ∀ n, ι n → ι n) (read : ∀ n, ι (n + 1) → Set (ι n))
    (hconj : ∀ n (v : G) (U : ι n → G), B n (fun b => v * U b * v⁻¹) = fun c => v * B n U c * v⁻¹)
    (hflip : ∀ n U, B n (flipOn z (S n) U) = flipOn z (S (n + 1)) (B n U))
    (hrot : ∀ n U, B n (U ∘ ρ n) = B n U ∘ ρ (n + 1))
    (hloc : ∀ n (U : ι n → G) c, (∀ b ∈ read n c, U b = 1) → B n U c = 1)
    (hread : ∀ n c, c ∉ S (n + 1) → ∀ b ∈ read n c, b ∉ S n)
    (U₀ : ι 0 → G) (hUc : ∀ b (g : G), g * U₀ b = U₀ b * g) (hUr : U₀ ∘ ρ 0 = flipOn z (S 0) U₀)
    (h₀ : ∀ b, b ∉ S 0 → U₀ b = 1) (n : ℕ) {c c₂ c₃ : ι n} (hc : c ∈ S n) (h₂ : c₂ ∉ S n) (h₃ : c₃ ∉ S n) :
    blockTower ι B U₀ n c * blockTower ι B U₀ n c₂ * (blockTower ι B U₀ n c₃)⁻¹
      * (blockTower ι B U₀ n (ρ n c))⁻¹ = z⁻¹ :=
  vortex_plaquette z (S n) (ρ n) _ (blockTower_vortex ι B z S ρ hconj hflip hrot U₀ hUc hUr n).2 hc
    (blockTower_trivial_off ι B S read hloc hread U₀ h₀ n c₂ h₂)
    (blockTower_trivial_off ι B S read hloc hread U₀ h₀ n c₃ h₃)

/-! ## SU(2): the central involution `-1` -/

/-- `-1 ∈ SU(2)`. -/
def su2NegOne : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨-1, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]; simp
    · simp [Matrix.det_neg]⟩

theorem su2_negOne_central (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) : su2NegOne * g = g * su2NegOne := by
  apply Subtype.ext
  simp [su2NegOne]

theorem su2_negOne_ne_one : su2NegOne ≠ 1 := by
  intro h
  have := congrArg (fun A : Matrix.specialUnitaryGroup (Fin 2) ℂ => (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  simp [su2NegOne] at this
  norm_num at this

theorem su2_negOne_inv : su2NegOne⁻¹ = su2NegOne := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  simp [su2NegOne]

end ProofPhase.M1
