/-
Proof phase, crossover workstream (c9a-crossover): the owner's refinement of the dichotomy, "uniform over every
well-defined outside", tested against null sets (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/DICHOTOMY.md`, section 8.
-/

import Mathlib

/-!
# A uniform bound on a full-measure set needs the cost to be bounded away from zero almost surely

The pattern-conditioned assembly (`Adjoint2/PatternAssembly.lean`, `FineOneBoxPat`) needs influence bounds only on a set of
full measure, so a null set of outsides can be disregarded for free. The question is whether the obstruction of the
dichotomy (the sheet cost `β|tr U_p|` vanishes at the SO(3) cut) can be removed by a null set.

* **`exists_mem_of_full_of_pos`** (S): a set of full measure meets every set of positive measure.
* **`no_uniform_lower_bound_on_full`** (S): if a cost `f` has `μ{f < c} > 0` for every `c > 0` (its essential infimum is
  `0`), then on **every** set of full measure and for **every** `c > 0` there are points with `f < c`. So no uniform positive
  lower bound, and with it no uniform Peierls weight bound, holds on any full-measure set.
* **`not_exists_full_with_bound`** (S): the same, as a non-existence statement.

**Claim level.** Lean, generic. The Yang-Mills input (paper, DICHOTOMY.md 8.2): for SU(2) with any law that has a positive
continuous density with respect to Haar measure near the cut (the Wilson measure and every conditional box law of it), the
sublevel sets `{β|tr U_p| < c}` have positive measure for every `c > 0`, because they contain a nonempty open set and Haar
measure charges open sets.
-/

open MeasureTheory

namespace ProofPhase.Crossover

variable {X : Type*} [MeasurableSpace X]

/-- A set of full measure meets every set of positive measure. -/
theorem exists_mem_of_full_of_pos (μ : Measure X) {Ω A : Set X} (hΩ : μ Ωᶜ = 0) (hA : μ A ≠ 0) :
    ∃ x ∈ Ω, x ∈ A := by
  by_contra h
  have hsub : A ⊆ Ωᶜ := fun x hx hxΩ => h ⟨x, hxΩ, hx⟩
  exact hA (measure_mono_null hsub hΩ)

/-- **No uniform positive lower bound on a full-measure set** (S): if every sublevel set `{f < c}`, `c > 0`, has positive
measure, then every full-measure set contains points with `f < c`, for every `c > 0`. -/
theorem no_uniform_lower_bound_on_full (μ : Measure X) (f : X → ℝ) (hpos : ∀ c > 0, μ {x | f x < c} ≠ 0)
    {Ω : Set X} (hΩ : μ Ωᶜ = 0) {c : ℝ} (hc : 0 < c) : ∃ x ∈ Ω, f x < c :=
  exists_mem_of_full_of_pos μ hΩ (hpos c hc)

/-- **No full-measure set carries a uniform positive bound** (S). -/
theorem not_exists_full_with_bound (μ : Measure X) (f : X → ℝ) (hpos : ∀ c > 0, μ {x | f x < c} ≠ 0) :
    ¬ ∃ Ω : Set X, μ Ωᶜ = 0 ∧ ∃ c > 0, ∀ x ∈ Ω, c ≤ f x := by
  rintro ⟨Ω, hΩ, c, hc, hb⟩
  obtain ⟨x, hx, hfx⟩ := no_uniform_lower_bound_on_full μ f hpos hΩ hc
  exact absurd (hb x hx) (not_le.2 hfx)

end ProofPhase.Crossover
