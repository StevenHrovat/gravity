/-
Round 2, attempt B: the reflection-positive coupling (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/r2-coupling/NOTE.md`, sections 3 and 4.
-/

import Mathlib

/-!
# The split label of the soft swap, and why it is optimal

**Split (`orbitMin`, `splitW`).** A finite group `M` of "mixings" acts on the local pair configurations `y` of one
interaction term (for a plaquette: the 2⁴ ways of exchanging its four links between the two replicas). The pair weight
`W(y) = φ(U_p) φ(U'_p)` is split as `W = κ + (W - κ)` with `κ = min over the M-orbit of W`. Both parts are `≥ 0`, `κ` is
invariant under **every** mixing (`splitW_false_inv`), and `W - κ` under every mixing that fixes `W` (the full swap,
`splitW_true_inv`). Attaching a label `t ∈ {0, 1}` with weight `κ` or `W - κ` gives an extended measure whose replica
marginal is unchanged (`splitW_sum`) and on which any partial swap is measure preserving as long as all terms it cuts
carry label `0` (NOTE §3).

**Optimality (`admissible_le_overlap`, `overlap_eq`).** On a finite space, any event on which an involution `S`
preserves the weights has mass at most the overlap `Σ min(p, p ∘ S) = 1 - TV(p, p ∘ S)`. The split attains this bound
term by term. So the probability that a given swap is admissible can never exceed `1 - TV(ν, S_* ν)`, whatever
auxiliary construction is used (NOTE §4).
-/

namespace Attempts.R2

open Finset

section OrbitMin

variable {M Y : Type*} [Group M] [Fintype M] [MulAction M Y]

/-- The minimum of `W` over the `M`-orbit of `y`. -/
noncomputable def orbitMin (W : Y → ℝ) (y : Y) : ℝ :=
  (univ : Finset M).inf' ⟨1, mem_univ _⟩ (fun m => W (m • y))

theorem orbitMin_le_smul (W : Y → ℝ) (y : Y) (m : M) : orbitMin (M := M) W y ≤ W (m • y) :=
  Finset.inf'_le (fun m : M => W (m • y)) (mem_univ m)

theorem orbitMin_le (W : Y → ℝ) (y : Y) : orbitMin (M := M) W y ≤ W y := by
  have h := orbitMin_le_smul (M := M) W y 1
  rwa [one_smul] at h

theorem le_orbitMin {W : Y → ℝ} {y : Y} {c : ℝ} (h : ∀ m : M, c ≤ W (m • y)) : c ≤ orbitMin (M := M) W y :=
  Finset.le_inf' _ _ fun m _ => h m

/-- **The orbit minimum is invariant under every mixing.** -/
theorem orbitMin_smul (W : Y → ℝ) (m : M) (y : Y) : orbitMin (M := M) W (m • y) = orbitMin (M := M) W y := by
  apply le_antisymm
  · apply le_orbitMin
    intro m'
    have h := orbitMin_le_smul (M := M) W (m • y) (m' * m⁻¹)
    rwa [mul_smul, inv_smul_smul] at h
  · apply le_orbitMin
    intro m'
    have h := orbitMin_le_smul (M := M) W y (m' * m)
    rwa [mul_smul] at h

theorem orbitMin_nonneg {W : Y → ℝ} (hW : ∀ y, 0 ≤ W y) (y : Y) : 0 ≤ orbitMin (M := M) W y :=
  le_orbitMin fun _ => hW _

/-- The two split weights: label `false` (inactive) carries `κ = orbitMin W`, label `true` (active) carries
    `W - κ`. -/
noncomputable def splitW (W : Y → ℝ) : Bool → Y → ℝ
  | false, y => orbitMin (M := M) W y
  | true, y => W y - orbitMin (M := M) W y

theorem splitW_nonneg {W : Y → ℝ} (hW : ∀ y, 0 ≤ W y) (b : Bool) (y : Y) : 0 ≤ splitW (M := M) W b y := by
  cases b
  · exact orbitMin_nonneg hW y
  · exact sub_nonneg.mpr (orbitMin_le W y)

/-- **Summing out the label returns the pair weight** (the replica marginal is unchanged). -/
theorem splitW_sum (W : Y → ℝ) (y : Y) : splitW (M := M) W false y + splitW (M := M) W true y = W y := by
  simp only [splitW]; ring

/-- **The inactive weight is invariant under every mixing.** -/
theorem splitW_false_inv (W : Y → ℝ) (m : M) (y : Y) : splitW (M := M) W false (m • y) = splitW (M := M) W false y :=
  orbitMin_smul W m y

/-- **The active weight is invariant under every mixing that fixes `W`** (e.g. the full swap of the replicas). -/
theorem splitW_true_inv {W : Y → ℝ} {m : M} (hm : ∀ y, W (m • y) = W y) (y : Y) :
    splitW (M := M) W true (m • y) = splitW (M := M) W true y := by
  simp only [splitW, hm y, orbitMin_smul]

/-- **Deterministic lower bound on the inactive fraction:** `a ≤ W ≤ b` gives `κ / W ≥ a / b`. -/
theorem orbitMin_ratio {W : Y → ℝ} {a b : ℝ} (ha : 0 < a) (hlow : ∀ y, a ≤ W y) (hup : ∀ y, W y ≤ b) (y : Y) :
    a / b ≤ orbitMin (M := M) W y / W y := by
  have hWy : 0 < W y := ha.trans_le (hlow y)
  have hb : 0 < b := hWy.trans_le (hup y)
  have hk : a ≤ orbitMin (M := M) W y := le_orbitMin fun _ => hlow _
  rw [div_le_div_iff₀ hb hWy]
  exact mul_le_mul hk (hup y) hWy.le (ha.le.trans hk)

end OrbitMin

section Optimal

variable {Ω : Type*} [Fintype Ω]

/-- **No admissible event beats the overlap.** If an event `A` is such that the involution `S` preserves the weight
    `p` pointwise on `A`, then `p(A) ≤ Σ min(p, p ∘ S)`. -/
theorem admissible_le_overlap (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (S : Ω → Ω) (A : Finset Ω)
    (hA : ∀ ω ∈ A, p (S ω) = p ω) : ∑ ω ∈ A, p ω ≤ ∑ ω, min (p ω) (p (S ω)) := by
  have h1 : ∑ ω ∈ A, p ω = ∑ ω ∈ A, min (p ω) (p (S ω)) :=
    Finset.sum_congr rfl fun ω hω => by rw [hA ω hω, min_self]
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ A) fun ω _ _ => le_min (hp ω) (hp (S ω))

omit [Fintype Ω] in
/-- The overlap weight `min(p, p ∘ S)` is `S`-invariant for an involution: the split attains the bound. -/
theorem overlap_inv (p : Ω → ℝ) {S : Ω → Ω} (hS : Function.Involutive S) (ω : Ω) :
    min (p (S ω)) (p (S (S ω))) = min (p ω) (p (S ω)) := by
  rw [hS ω, min_comm]

/-- **The overlap is one minus the total variation** between `p` and `p ∘ S` (for a probability weight and an
    involution). -/
theorem overlap_eq (p : Ω → ℝ) (hsum : ∑ ω, p ω = 1) {S : Ω → Ω} (hS : Function.Involutive S) :
    ∑ ω, min (p ω) (p (S ω)) = 1 - (1 / 2) * ∑ ω, |p ω - p (S ω)| := by
  have hpt : ∀ a b : ℝ, min a b = (a + b - |a - b|) / 2 := by
    intro a b
    rcases le_total a b with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  have hcomp : ∑ ω, p (S ω) = ∑ ω, p ω := Equiv.sum_comp (Function.Involutive.toPerm S hS) p
  simp_rw [hpt]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hcomp, hsum]
  ring

end Optimal

end Attempts.R2
