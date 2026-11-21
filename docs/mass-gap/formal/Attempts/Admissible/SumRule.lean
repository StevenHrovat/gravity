/-
Attempt round 2026-11-21, route (c) "admissible". Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/admissible/NOTE.md`, section 4 (the sum rule).
-/

import OneScale.Blocks

/-!
# Telescoping influence bounds over several boundary coordinates (the formal half of the sum rule)

`influence_telescope`: if the configurations `σ, σ'` differ only on a finite set `T` of coordinates, and `k z` is an
influence bound (`OneScale.IsInfluenceBound`) of the block specification `q` for every `z ∈ T`, then for every test
function `F` of the block with single-coordinate oscillations at most `L`:

  `|q^σ(F) − q^{σ'}(F)| ≤ (∑_{z ∈ T} k z) · L`.

The same with the Lipschitz (W) form of the proof note (`IsInfluenceBoundW`, cost `k · ρ(σ z, s)` for a change of `z`):
`influence_telescopeW`, `|q^σ(F) − q^{σ'}(F)| ≤ (∑_{z ∈ T} k z · ρ(σ z, σ' z)) · L`.

**Use (NOTE §4).** Take `T` = the shell links of one direction `ν` and `σ' = g·σ` for the boundary gauge transformation
`g_x = exp(i c X x_ν)` (a constant flat connection in direction `ν`, every shell `ν`-link moved by `ρ = |c|`). The left
side is the response of the block to a pure gauge shift of its whole boundary, which at weak coupling moves every open
Wilson line across the box in direction `ν` by `ℓ c`. With the line functional `F` (one 1-Lipschitz term per line, so
`L = 1` per link) the W form gives `∑_{y ∈ shell, dir ν} k^W(y) ≥ #{ν-links of the block} · (1 − o(1))`, i.e.
`γ_W ≥ 1 − o(1)`: GDS_W fails at weak coupling on every box of fixed size, for every compact connected gauge group,
admissible or not. The concentration step (`o(1)` as `β → ∞` at fixed box size, a finite-dimensional Laplace argument)
is not formalised; this file only supplies the telescoping.
-/

open MeasureTheory Finset

noncomputable section

namespace Attempts.Admissible

open OneScale

variable {ι S : Type*} [DecidableEq ι] [MeasurableSpace S]

/-- **Telescoping of influence bounds** over a finite set of changed coordinates. -/
theorem influence_telescope {B : Finset ι} {q : (ι → S) → Measure (ι → S)} (k : ι → ℝ) (T : Finset ι)
    (hk : ∀ z ∈ T, IsInfluenceBound B q z (k z)) {F : (ι → S) → ℝ} {L : ℝ} (hF : BM F) (hdep : DepOn F B)
    (hL : ∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) :
    ∀ σ σ' : ι → S, (∀ i ∉ T, σ i = σ' i) →
      |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q σ')| ≤ (∑ z ∈ T, k z) * L := by
  induction T using Finset.induction_on with
  | empty =>
    intro σ σ' h
    have : σ = σ' := funext fun i => h i (Finset.notMem_empty i)
    subst this
    simp
  | insert a T ha ih =>
    intro σ σ' h
    -- change the coordinate `a` first, then the rest
    set τ := Function.update σ a (σ' a)
    have h1 : |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q τ)| ≤ k a * L :=
      hk a (Finset.mem_insert_self a T) σ (σ' a) F L hF hdep hL
    have h2 : |∫ ξ, F ξ ∂(q τ) - ∫ ξ, F ξ ∂(q σ')| ≤ (∑ z ∈ T, k z) * L := by
      refine ih (fun z hz => hk z (Finset.mem_insert_of_mem hz)) τ σ' fun i hi => ?_
      by_cases hia : i = a
      · subst hia; simp [τ]
      · simp only [τ, Function.update_of_ne hia]
        exact h i (by simp [hia, hi])
    rw [Finset.sum_insert ha, add_mul]
    calc _ ≤ |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q τ)| + |∫ ξ, F ξ ∂(q τ) - ∫ ξ, F ξ ∂(q σ')| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add h1 h2

/-! ## The Lipschitz (W) form

The framework's `IsInfluenceBound` is the oscillation (H) form. The sum rule bites in the Lipschitz (W) form of the proof
note (§1.6, `k^W`), where a change of the coordinate `z` from `σ z` to `s` costs `k · ρ(σ z, s)`. We state that form here
for a general cost `ρ : S → S → ℝ` and telescope it the same way. -/

/-- **Lipschitz-form influence bound** (PROOF-NOTE §1.6, `k^W_B(z)`): for every bounded measurable `F` of the block that is
    `L`-Lipschitz in each block coordinate for `ρ`, changing the outside coordinate `z` from `σ z` to `s` moves the block
    expectation by at most `k · ρ(σ z, s) · L`. -/
def IsInfluenceBoundW (ρ : S → S → ℝ) (B : Finset ι) (q : (ι → S) → Measure (ι → S)) (z : ι) (k : ℝ) : Prop :=
  ∀ (σ : ι → S) (s : S) (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B →
    (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L * ρ (ξ y) t) →
    |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q (Function.update σ z s))| ≤ k * ρ (σ z) s * L

/-- **Telescoping in the Lipschitz form**: `|q^σ(F) − q^{σ'}(F)| ≤ ∑_{z ∈ T} k z · ρ(σ z, σ' z) · L`. -/
theorem influence_telescopeW (ρ : S → S → ℝ) {B : Finset ι} {q : (ι → S) → Measure (ι → S)} (k : ι → ℝ)
    (T : Finset ι) (hk : ∀ z ∈ T, IsInfluenceBoundW ρ B q z (k z)) {F : (ι → S) → ℝ} {L : ℝ} (hF : BM F)
    (hdep : DepOn F B) (hL : ∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L * ρ (ξ y) t) :
    ∀ σ σ' : ι → S, (∀ i ∉ T, σ i = σ' i) →
      |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q σ')| ≤ (∑ z ∈ T, k z * ρ (σ z) (σ' z)) * L := by
  induction T using Finset.induction_on with
  | empty =>
    intro σ σ' h
    have : σ = σ' := funext fun i => h i (Finset.notMem_empty i)
    subst this
    simp
  | insert a T ha ih =>
    intro σ σ' h
    set τ := Function.update σ a (σ' a)
    have h1 : |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q τ)| ≤ k a * ρ (σ a) (σ' a) * L :=
      hk a (Finset.mem_insert_self a T) σ (σ' a) F L hF hdep hL
    have hτ : ∀ z ∈ T, τ z = σ z := fun z hz => by
      have : z ≠ a := fun e => ha (e ▸ hz)
      simp [τ, Function.update_of_ne this]
    have h2 : |∫ ξ, F ξ ∂(q τ) - ∫ ξ, F ξ ∂(q σ')| ≤ (∑ z ∈ T, k z * ρ (τ z) (σ' z)) * L := by
      refine ih (fun z hz => hk z (Finset.mem_insert_of_mem hz)) τ σ' fun i hi => ?_
      by_cases hia : i = a
      · subst hia; simp [τ]
      · simp only [τ, Function.update_of_ne hia]
        exact h i (by simp [hia, hi])
    rw [Finset.sum_congr rfl fun z hz => by rw [hτ z hz]] at h2
    rw [Finset.sum_insert ha, add_mul]
    calc _ ≤ |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q τ)| + |∫ ξ, F ξ ∂(q τ) - ∫ ξ, F ξ ∂(q σ')| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add h1 h2

end Attempts.Admissible
