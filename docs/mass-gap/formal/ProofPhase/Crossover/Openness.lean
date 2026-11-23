/-
Proof phase, cycle 9, workstream a (c9a-crossover): openness of the one-box criterion under perturbation of the box laws,
and the finite-net form a certification would use (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/NOTE.md`, section 2.4.
-/

import ProofPhase.OneBox.Criterion

/-!
# The one-box criterion is open: what precision a reduction or a certification of P4 needs

The crossover P4 has to put the law at `L₁` inside the one-box window. Any argument that gets there by approximation (a
truncated effective action, a finite net over a class of inputs, a computed enclosure) needs the criterion to be **open**:
a box specification that is uniformly close to one satisfying the criterion satisfies it too, with a budget loss that can be
named. This file proves that, generically.

* `IsNearSpec B q q' δ`: for **every** boundary condition `σ` and every bounded measurable test function `F` of the box `B`
  with oscillation `≤ L` per site, `|∫ F d(q σ) − ∫ F d(q' σ)| ≤ δ L`. (A Wasserstein distance between the two box laws
  in the "number of differing sites" metric, worst case over boundary conditions; `δ` is extensive in the box.)
* `isInfluenceBoundOn_of_near` (S): an influence bound `k` for `q` gives the influence bound `k + 2δ` for `q'` (three-term
  triangle inequality; the worst case over boundary conditions is what makes it work).
* `oneBoxSum_of_near` (S): if the perturbation adds at most `2δ` to the influence numbers on a shell `sh` of positions and
  nothing elsewhere, the one-box sum survives with `γ + 2δ S/|Λ₀|`, `S` the weighted size of the shell.
* `influence_of_net` (S): a family of specifications indexed by `θ`, each within `δ` of some member of a finite net whose
  influences are bounded by common numbers `κ̄`, has influences `κ̄ + 2δ`: **the criterion over a class follows from the
  criterion on a net plus a closeness bound**. This is the logical form of a finite-system reduction of P4; the content is
  in the closeness bound (`IsNearSpec` uniformly over the class), not here.

**Claim level.** Generic and elementary (Lean, S); no Yang–Mills content. The size it fixes: with a shell of `|sh|` positions
around a box of `|Λ₀|` sites and `λ = 0`, closeness `δ` costs `2δ |sh| / |Λ₀|` of the budget, so a margin `1 − γ` survives
iff `δ < (1 − γ)|Λ₀| / (2|sh|)`; for a cube of side `ℓ` with a one-cell shell (`|sh| ≈ 8ℓ³`) this is `δ ≲ (1 − γ) ℓ / 16`
differing sites in total per box law, i.e. about `(1 − γ)/(16 ℓ³)` per site.
-/

open MeasureTheory Finset OneScale ProofPhase.OneBox

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Crossover

section Near

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-- **Two box specifications are `δ`-close, worst case over boundary conditions**: for every boundary condition and every
bounded measurable test function of the box with oscillation `≤ L` per site, the two expectations differ by `≤ δ L`. -/
def IsNearSpec (B : Finset ι) (q q' : (ι → S) → Measure (ι → S)) (δ : ℝ) : Prop :=
  ∀ (σ : ι → S) (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B →
    (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) →
    |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q' σ)| ≤ δ * L

theorem isNearSpec_symm {B : Finset ι} {q q' : (ι → S) → Measure (ι → S)} {δ : ℝ} (h : IsNearSpec B q q' δ) :
    IsNearSpec B q' q δ := by
  intro σ F L hF hdep hosc
  rw [abs_sub_comm]; exact h σ F L hF hdep hosc

/-- **Openness of an influence bound** (S): closeness `δ` of the box laws, uniformly over boundary conditions, costs at most
`2δ` of influence, on any admissible class. -/
theorem isInfluenceBoundOn_of_near {Adm : (ι → S) → ((ι → S) → ℝ) → Prop} {B : Finset ι}
    {q q' : (ι → S) → Measure (ι → S)} {z : ι} {k δ : ℝ} (hk : IsInfluenceBoundOn Adm B q z k)
    (hn : IsNearSpec B q q' δ) : IsInfluenceBoundOn Adm B q' z (k + 2 * δ) := by
  intro σ s F L hF hdep hadm hosc
  have h1 := hn σ F L hF hdep hosc
  have h2 := hk σ s F L hF hdep hadm hosc
  have h3 := hn (Function.update σ z s) F L hF hdep hosc
  calc |∫ ξ, F ξ ∂(q' σ) - ∫ ξ, F ξ ∂(q' (Function.update σ z s))|
      ≤ |∫ ξ, F ξ ∂(q' σ) - ∫ ξ, F ξ ∂(q σ)| + |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q (Function.update σ z s))|
        + |∫ ξ, F ξ ∂(q (Function.update σ z s)) - ∫ ξ, F ξ ∂(q' (Function.update σ z s))| := by
        have := abs_sub_le (∫ ξ, F ξ ∂(q' σ)) (∫ ξ, F ξ ∂(q σ)) (∫ ξ, F ξ ∂(q' (Function.update σ z s)))
        have h' := abs_sub_le (∫ ξ, F ξ ∂(q σ)) (∫ ξ, F ξ ∂(q (Function.update σ z s)))
          (∫ ξ, F ξ ∂(q' (Function.update σ z s)))
        linarith
    _ ≤ δ * L + k * L + δ * L := by
        rw [abs_sub_comm] at h1
        exact add_le_add (add_le_add h1 h2) h3
    _ = (k + 2 * δ) * L := by ring

/-- **The criterion over a class from the criterion on a finite net** (S). A family of box specifications `qθ`, each
`δ`-close (worst case over boundary conditions) to some member `qθ (c θ)` of a net `Θ₀` whose influences at `z` are bounded
by `κbar`, has influences `κbar + 2δ` at `z`. (Finiteness of the net is what makes the premise checkable; it is not used.) -/
theorem influence_of_net {Θ : Type*} {Adm : (ι → S) → ((ι → S) → ℝ) → Prop} {B : Finset ι}
    (qθ : Θ → (ι → S) → Measure (ι → S)) (Θ₀ : Set Θ) (c : Θ → Θ) (hc : ∀ θ, c θ ∈ Θ₀) {z : ι} {κbar δ : ℝ}
    (hnet : ∀ θ₀ ∈ Θ₀, IsInfluenceBoundOn Adm B (qθ θ₀) z κbar)
    (hnear : ∀ θ, IsNearSpec B (qθ (c θ)) (qθ θ) δ) (θ : Θ) :
    IsInfluenceBoundOn Adm B (qθ θ) z (κbar + 2 * δ) :=
  isInfluenceBoundOn_of_near (hnet (c θ) (hc θ)) (hnear θ)

end Near

section Budget

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **The one-box sum survives a perturbation on a shell** (S). If `κ' u ≤ κ u + 2δ` on the shell `sh` and `κ' u ≤ κ u`
off it, and the weighted shell size is `∑_{u ∈ sh, u ∉ Λ₀} e^{λ Ê(u)} ≤ S`, then the one-box sum holds for `κ'` with
`γ + 2δ S / |Λ₀|`. -/
theorem oneBoxSum_of_near {κ κ' Ehat : U → ℝ} {Λ₀ : Finset U} {lam γ δ S : ℝ} (sh : Finset U)
    (hδ : 0 ≤ δ) (hΛ : 0 < Λ₀.card) (h : OneBoxSum κ Ehat Λ₀ lam γ)
    (hsh : ∀ u ∈ sh, κ' u ≤ κ u + 2 * δ) (hoff : ∀ u ∉ sh, κ' u ≤ κ u)
    (hS : ∑ u ∈ (univ.filter (fun u => u ∉ Λ₀)).filter (fun u => u ∈ sh), Real.exp (lam * Ehat u) ≤ S) :
    OneBoxSum κ' Ehat Λ₀ lam (γ + 2 * δ * S / Λ₀.card) := by
  unfold OneBoxSum at *
  set O := univ.filter (fun u : U => u ∉ Λ₀)
  have hcard : (0 : ℝ) < Λ₀.card := by exact_mod_cast hΛ
  have hpt : ∀ u ∈ O, κ' u * Real.exp (lam * Ehat u) ≤
      κ u * Real.exp (lam * Ehat u) + (if u ∈ sh then 2 * δ * Real.exp (lam * Ehat u) else 0) := by
    intro u _
    have he := (Real.exp_pos (lam * Ehat u)).le
    by_cases hu : u ∈ sh
    · simp only [hu, ↓reduceIte]
      nlinarith [hsh u hu]
    · simp only [hu, ↓reduceIte, add_zero]
      exact mul_le_mul_of_nonneg_right (hoff u hu) he
  have hsplit : ∑ u ∈ O, (if u ∈ sh then 2 * δ * Real.exp (lam * Ehat u) else 0) =
      2 * δ * ∑ u ∈ O.filter (fun u => u ∈ sh), Real.exp (lam * Ehat u) := by
    rw [← sum_filter, mul_sum]
  calc ∑ u ∈ O, κ' u * Real.exp (lam * Ehat u)
      ≤ ∑ u ∈ O, (κ u * Real.exp (lam * Ehat u) + (if u ∈ sh then 2 * δ * Real.exp (lam * Ehat u) else 0)) :=
        sum_le_sum hpt
    _ = ∑ u ∈ O, κ u * Real.exp (lam * Ehat u) + 2 * δ * ∑ u ∈ O.filter (fun u => u ∈ sh), Real.exp (lam * Ehat u) := by
        rw [sum_add_distrib, hsplit]
    _ ≤ γ * Λ₀.card + 2 * δ * S := by
        have : 2 * δ * ∑ u ∈ O.filter (fun u => u ∈ sh), Real.exp (lam * Ehat u) ≤ 2 * δ * S :=
          mul_le_mul_of_nonneg_left hS (by linarith)
        linarith
    _ = (γ + 2 * δ * S / Λ₀.card) * Λ₀.card := by
        field_simp

/-- **The precision a certification needs** (S): the perturbed criterion keeps a margin iff `2δS < (1 − γ)|Λ₀|`. -/
theorem near_budget_lt_one {γ δ S : ℝ} {n : ℕ} (hn : 0 < n) (h : 2 * δ * S < (1 - γ) * n) :
    γ + 2 * δ * S / n < 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : 2 * δ * S / n < 1 - γ := by rw [div_lt_iff₀ hn']; linarith
  linarith

end Budget

end ProofPhase.Crossover
