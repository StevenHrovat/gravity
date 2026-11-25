/-
Attempt r3-dmp (round 3, attempt 5), 2026-11-21. Released under Apache 2.0.

# The bridge "DMP-complete ⇒ a continuum limit exists", made precise

The owner's idea: "If we can show that YM is a subset of DMP, we can offer an alternative route to the existence proof of OAI."
Note: `docs/mass-gap/weak-coupling/attempts/r3-dmp/NOTE.md`.

DMP-complete (`evidence/Dmp/Complete.lean`, `Recipe.dmpComplete`) is a predicate on a *finite* recipe (`r.n` lines) together with a
lemma ledger `agree : Nat → Bool`: well formed, and every line carried. The `evidence/` DMP project is a separate Lean project; the
definition is restated here (`Ledger.complete`) in the same shape, with well-formedness kept abstract as a proposition.

What this file proves, about the logic of the bridge (no Yang–Mills input):

1. **Per-level completeness gives no limit** (`perLevel_no_limit`). If two different objects satisfy a per-level predicate, the
   sequence that alternates between them satisfies the predicate at every level and converges to nothing. So "every regularised theory
   is DMP-complete" (each a finite, certified object) cannot be the existence theorem for the continuum: the bridge needs a statement
   that couples the levels.
2. **A uniform certificate gives existence along a subsequence** (`exists_of_uniform_certificate`). If every level lies in one compact
   set (the certificate's constants are the same at every level: "This holds at every layer", read uniformly) and in a closed set of
   structural properties (reflection positivity and lattice symmetries are closed conditions), a subsequence converges and the limit
   keeps the closed properties. This is the shape of the OpenAI existence proof (uniform bounds, compactness, subsequence).
3. **Non-triviality is not closed, so it is lost in limits unless it has a uniform margin** (`margin_lost_in_limit`,
   `nontrivial_of_uniform_margin`). A quantity positive at every level can tend to zero: this is φ⁴ in four dimensions (Aizenman and
   Duminil-Copin 2021: non-Gaussian at every cutoff, Gaussian in the limit). A positive lower bound *uniform in the level* passes to the
   limit. So the bridge can deliver non-triviality only from a uniform margin, which is content (asymptotic freedom), not structure.
4. **Restated ledger facts** (`Ledger.complete_allYes_iff`, `Ledger.empty_complete`): under the all-yes ledger, completeness is
   well-formedness alone (cf. `Refute.rf_dmpComplete_is_the_ledger`), and the empty configuration is complete (cf.
   `Cmb.empty_recipe_proven`): the trivial theory passes every DMP check. DMP's Axiom 3 says the same in its own words: "From trust
   nothing can be derived about information but its existence".
-/

import Mathlib

open Filter Topology

namespace Attempts.R3.DmpHost

/-! ## 0. The DMP side, restated -/

/-- A configuration as Gravity checks it: `n` lines, a well-formedness proposition, and the lemma ledger's answer per line. Restated
    from `evidence/Dmp/Recipe.lean` and `Complete.lean` (separate Lean project). -/
structure Ledger where
  n : ℕ
  wf : Prop
  agree : ℕ → Bool

/-- DMP-complete: well formed, and every line carried by both chains (`Recipe.dmpComplete`). -/
def Ledger.complete (r : Ledger) : Prop := r.wf ∧ ∀ i, i < r.n → r.agree i = true

/-- Under the all-yes ledger, completeness is well-formedness and nothing more (`Refute.rf_dmpComplete_is_the_ledger`): the content of
    "DMP-complete" is exactly the content of the ledger. -/
theorem Ledger.complete_allYes_iff (n : ℕ) (wf : Prop) : (Ledger.mk n wf fun _ => true).complete ↔ wf := by
  simp [Ledger.complete]

/-- The empty configuration is complete under any ledger (`Cmb.empty_recipe_proven`): a configuration in which nothing happens passes. -/
theorem Ledger.empty_complete (agree : ℕ → Bool) : (Ledger.mk 0 True agree).complete := by
  simp [Ledger.complete]

/-! ## 1. Per-level completeness gives no limit -/

/-- The sequence that alternates between `x` (even levels) and `y` (odd levels). -/
noncomputable def alternate {X : Type*} (x y : X) (k : ℕ) : X := if Even k then x else y

theorem alternate_even {X : Type*} (x y : X) (k : ℕ) : alternate x y (2 * k) = x := by
  simp [alternate]

theorem alternate_odd {X : Type*} (x y : X) (k : ℕ) : alternate x y (2 * k + 1) = y := by
  simp [alternate]

/-- **Per-level completeness gives no limit.** In a Hausdorff space, for any predicate `P` (here: "the regularised theory at this level
    is DMP-complete") satisfied by two different objects, there is a sequence satisfying `P` at every level that has no limit. -/
theorem perLevel_no_limit {X : Type*} [TopologicalSpace X] [T2Space X] (P : X → Prop) {x y : X} (hx : P x) (hy : P y)
    (hxy : x ≠ y) : ∃ s : ℕ → X, (∀ k, P (s k)) ∧ ¬ ∃ z, Tendsto s atTop (𝓝 z) := by
  refine ⟨alternate x y, fun k => ?_, ?_⟩
  · unfold alternate; split_ifs
    · exact hx
    · exact hy
  · rintro ⟨z, hz⟩
    have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
      tendsto_id.const_mul_atTop' (by norm_num : (0 : ℕ) < 2)
    have h21 : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp h2
    have he : Tendsto (fun k => alternate x y (2 * k)) atTop (𝓝 z) := hz.comp h2
    have ho : Tendsto (fun k => alternate x y (2 * k + 1)) atTop (𝓝 z) := hz.comp h21
    simp only [alternate_even] at he
    simp only [alternate_odd] at ho
    have hxz : x = z := tendsto_nhds_unique tendsto_const_nhds he
    have hyz : y = z := tendsto_nhds_unique tendsto_const_nhds ho
    exact hxy (hxz.trans hyz.symm)

/-! ## 2. A uniform certificate gives existence along a subsequence -/

/-- **The reduced bridge.** In a metric space, if every level lies in one compact set `K` (a certificate with the same constants at
    every level) and in a closed set `F` (closed structural properties: reflection positivity, the lattice symmetries), then a
    subsequence converges, and its limit lies in `K ∩ F`. Existence along a subsequence, with the closed properties kept. -/
theorem exists_of_uniform_certificate {X : Type*} [MetricSpace X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F)
    (s : ℕ → X) (hsK : ∀ k, s k ∈ K) (hsF : ∀ k, s k ∈ F) :
    ∃ z ∈ K ∩ F, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (s ∘ φ) atTop (𝓝 z) := by
  obtain ⟨z, hzK, φ, hφ, hlim⟩ := hK.tendsto_subseq hsK
  exact ⟨z, ⟨hzK, hF.mem_of_tendsto hlim (Eventually.of_forall fun k => hsF (φ k))⟩, φ, hφ, hlim⟩

/-! ## 3. Non-triviality needs a uniform margin -/

/-- **A margin can be lost in the limit.** A quantity positive at every level (a renormalised coupling, a connected four-point
    function) can tend to zero. This is the shape of four-dimensional φ⁴: non-trivial at every cutoff, trivial in the limit. -/
theorem margin_lost_in_limit : ∃ g : ℕ → ℝ, (∀ k, 0 < g k) ∧ Tendsto g atTop (𝓝 0) :=
  ⟨fun k => 1 / ((k : ℝ) + 1), fun k => by positivity, tendsto_one_div_add_atTop_nhds_zero_nat⟩

/-- **A uniform margin survives.** If a continuous functional `f` (a renormalised coupling) is at least `c` at every level of a
    convergent sequence, it is at least `c` in the limit; with `c > 0` the limit is not the free theory (`f = 0` there). -/
theorem nontrivial_of_uniform_margin {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) {c : ℝ}
    {s : ℕ → X} {z : X} (hs : Tendsto s atTop (𝓝 z)) (hc : ∀ k, c ≤ f (s k)) : c ≤ f z :=
  ge_of_tendsto ((hf.tendsto z).comp hs) (Eventually.of_forall hc)

/-- The two together: closed structure and a uniform margin pass to a subsequential limit; positivity at every level alone does not. -/
theorem exists_nontrivial_of_uniform_certificate {X : Type*} [MetricSpace X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F)
    {f : X → ℝ} (hf : Continuous f) {c : ℝ} (hc0 : 0 < c) (s : ℕ → X) (hsK : ∀ k, s k ∈ K) (hsF : ∀ k, s k ∈ F)
    (hmargin : ∀ k, c ≤ f (s k)) :
    ∃ z ∈ K ∩ F, 0 < f z ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (s ∘ φ) atTop (𝓝 z) := by
  obtain ⟨z, hz, φ, hφ, hlim⟩ := exists_of_uniform_certificate hK hF s hsK hsF
  exact ⟨z, hz, lt_of_lt_of_le hc0 (nontrivial_of_uniform_margin hf hlim fun k => hmargin (φ k)), φ, hφ, hlim⟩

end Attempts.R3.DmpHost
