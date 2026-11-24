/-
The transport theorem, part 3: it is not empty (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/TRANSPORT.md`, section 4.
-/

import ProofPhase.Unified.Transport

/-!
# A model where everything is proved: a perturbed two-state Markov chain

**The model.** A two-state chain (states 0 and 1) with flip rates `α` (0 to 1) and `β` (1 to 0) acts on the law
`p = P(state 1)` by `step2 α β p = (1 − p) α + p (1 − β)`. A perturbed chain uses rates `α' n, β' n` at step `n`. The
**uncertainty** is the distance of the two laws, `|q n − p n|`; the **fresh uncertainty** of step `n` is the size of the
perturbation, `|α' n − α| + |β' n − β|`; the **factor** is Doeblin's `|1 − α − β|`.

* `doeblin_step`, `doeblin_transports` (Lean): the distance is a transport in the sense of `Transports`, floor `0`.
* `doeblin_example` (Lean, (a) + (c)): rates `1/4, 1/4` (factor `1/2`), perturbations at most `1/10` per step, both
  chains started at `1/2`: for every `n` the perturbed law stays in `[3/10, 7/10]`, so both states keep positive
  probability at every step: the sign is certified across every step, uniformly.
* `ident_chain`, `ident_margin_lost` (Lean, the critical case): with no mixing (`α = β = 0`, factor `1`, cost =
  floor) a perturbation of the same kind, `α' = ρ`, erases the margin: `P(state 0) = (1/2)(1 − ρ)^n → 0`.
  (`critical_sharp` in `Transport.lean` is the case where the bound of (b) is attained with equality.)

Standard axioms only.
-/

open Finset

noncomputable section

namespace ProofPhase.Unified

/-- One step of the two-state chain on the law `p = P(state 1)`. -/
def step2 (α β p : ℝ) : ℝ := (1 - p) * α + p * (1 - β)

/-- Rates in `[0, 1]` keep a law a law. -/
theorem step2_mem {α β p : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : 0 ≤ step2 α β p ∧ step2 α β p ≤ 1 := by
  have h1 : 0 ≤ 1 - p := by linarith
  have h2 : 0 ≤ 1 - β := by linarith
  have h3 := mul_le_mul_of_nonneg_left hα1 h1
  have h4 : p * (1 - β) ≤ p * 1 := mul_le_mul_of_nonneg_left (by linarith) hp0
  unfold step2
  constructor
  · exact add_nonneg (mul_nonneg h1 hα0) (mul_nonneg hp0 h2)
  · linarith

/-- **Doeblin's step with a perturbation**: `|q' − p'| ≤ |1 − α − β| |q − p| + (|α' − α| + |β' − β|)`. -/
theorem doeblin_step (α β α' β' p q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |step2 α' β' q - step2 α β p| ≤ |1 - α - β| * |q - p| + (|α' - α| + |β' - β|) := by
  have e : step2 α' β' q - step2 α β p = (1 - α - β) * (q - p) + ((1 - q) * (α' - α) + q * (β - β')) := by
    unfold step2; ring
  rw [e]
  have h1 : |(1 - q) * (α' - α)| ≤ |α' - α| := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - q)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
  have h2 : |q * (β - β')| ≤ |β' - β| := by
    rw [abs_mul, abs_of_nonneg hq0, abs_sub_comm]
    exact mul_le_of_le_one_left (abs_nonneg _) hq1
  have h3 := abs_add_le ((1 - α - β) * (q - p)) ((1 - q) * (α' - α) + q * (β - β'))
  have h4 := abs_add_le ((1 - q) * (α' - α)) (q * (β - β'))
  rw [abs_mul] at h3
  linarith

/-- The perturbed chain stays a law. -/
theorem perturbed_mem {α' β' q : ℕ → ℝ} (hq : ∀ n, q (n + 1) = step2 (α' n) (β' n) (q n))
    (hα' : ∀ n, 0 ≤ α' n ∧ α' n ≤ 1) (hβ' : ∀ n, 0 ≤ β' n ∧ β' n ≤ 1) (h0 : 0 ≤ q 0 ∧ q 0 ≤ 1) (n : ℕ) :
    0 ≤ q n ∧ q n ≤ 1 := by
  induction n with
  | zero => exact h0
  | succ n ih => rw [hq]; exact step2_mem (hα' n).1 (hα' n).2 (hβ' n).1 (hβ' n).2 ih.1 ih.2

/-- **The distance of the two chains is a transported uncertainty** (floor `0`, factor `|1 − α − β|`, fresh
uncertainty the perturbation). -/
theorem doeblin_transports {α β : ℝ} {α' β' p q : ℕ → ℝ} (hp : ∀ n, p (n + 1) = step2 α β (p n))
    (hq : ∀ n, q (n + 1) = step2 (α' n) (β' n) (q n)) (hqm : ∀ n, 0 ≤ q n ∧ q n ≤ 1) (n : ℕ) :
    Transports (fun i => |q i - p i|) (fun _ => |1 - α - β|) (fun i => |α' i - α| + |β' i - β|) 0 n :=
  fun i _ => by
    show |q (i + 1) - p (i + 1)| ≤ Real.exp 0 * |1 - α - β| * |q i - p i| + (|α' i - α| + |β' i - β|)
    rw [Real.exp_zero, one_mul, hp, hq]
    exact doeblin_step _ _ _ _ _ _ (hqm i).1 (hqm i).2

/-- **(a) and (c) on a fully proved model.** Rates `1/4, 1/4`, perturbed rates in `[0, 1]` within `1/10` in total per
step, both chains started at `1/2`: for every `n`, `3/10 ≤ q n ≤ 7/10`. The uncertainty stays below
`0 + (1/10)/(1 − 1/2) = 1/5` uniformly (a), below the margin `1/2` of both states, so both keep positive probability (c). -/
theorem doeblin_example {α' β' q : ℕ → ℝ} (hq : ∀ n, q (n + 1) = step2 (α' n) (β' n) (q n))
    (hα' : ∀ n, 0 ≤ α' n ∧ α' n ≤ 1) (hβ' : ∀ n, 0 ≤ β' n ∧ β' n ≤ 1)
    (hpert : ∀ n, |α' n - 1 / 4| + |β' n - 1 / 4| ≤ 1 / 10) (h0 : q 0 = 1 / 2) (n : ℕ) :
    3 / 10 ≤ q n ∧ q n ≤ 7 / 10 := by
  have hqm := perturbed_mem hq hα' hβ' (by rw [h0]; norm_num)
  have hp : ∀ n, (fun _ : ℕ => (1 / 2 : ℝ)) (n + 1) = step2 (1 / 4) (1 / 4) ((fun _ : ℕ => (1 / 2 : ℝ)) n) :=
    fun _ => by simp only [step2]; norm_num
  have ht := doeblin_transports (α := 1 / 4) (β := 1 / 4) (p := fun _ => (1 / 2 : ℝ)) hp hq hqm n
  have hf : |(1 : ℝ) - 1 / 4 - 1 / 4| = 1 / 2 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hb := (bounded_transport (θ := 1 / 2) (R := 1 / 10) ht (fun _ => abs_nonneg _) (fun _ => hf.le)
    (by rw [Real.exp_zero]; norm_num) (fun _ => by positivity) hpert (abs_nonneg _)).2
  rw [h0, sub_self, abs_zero, Real.exp_zero] at hb
  have hb' : |q n - 1 / 2| ≤ 1 / 5 := by
    have : (0 : ℝ) + 1 / 10 / (1 - 1 * (1 / 2)) = 1 / 5 := by norm_num
    linarith
  have := abs_le.1 hb'
  constructor <;> linarith [this.1, this.2]

/-- **The critical case: no mixing.** With `α = β = 0` (factor `1`, cost = floor) and the perturbation `α' = ρ`,
started at `1/2`: `P(state 0) = 1 − q n = (1/2)(1 − ρ)^n`. -/
theorem ident_chain {ρ : ℝ} {q : ℕ → ℝ} (hq : ∀ n, q (n + 1) = step2 ρ 0 (q n)) (h0 : q 0 = 1 / 2) (n : ℕ) :
    1 - q n = 1 / 2 * (1 - ρ) ^ n := by
  induction n with
  | zero => rw [h0]; norm_num
  | succ n ih =>
    rw [hq, step2, pow_succ]
    linear_combination (1 - ρ) * ih

/-- **At cost = floor the margin is lost.** In the chain of `ident_chain` with `ρ > 0` (a law for `ρ ≤ 1`), the probability of state 0
falls below every `ε > 0`: a constant fresh uncertainty, never damped, eats the whole margin `1/2`. Under Doeblin
mixing a perturbation of the same size keeps it (`doeblin_example`). -/
theorem ident_margin_lost {ρ : ℝ} (hρ0 : 0 < ρ) {q : ℕ → ℝ} (hq : ∀ n, q (n + 1) = step2 ρ 0 (q n))
    (h0 : q 0 = 1 / 2) {ε : ℝ} (hε : 0 < ε) : ∃ n, 1 - q n < ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 2 * ε by linarith) (show 1 - ρ < 1 by linarith)
  exact ⟨n, by rw [ident_chain hq h0]; linarith⟩

/-- The no-mixing chain is a critical transport: its factor is `|1 − 0 − 0| = 1`, so `e^0 · 1 = 1`. -/
theorem ident_is_critical : Real.exp 0 * |(1 : ℝ) - 0 - 0| = 1 := by norm_num

end ProofPhase.Unified
