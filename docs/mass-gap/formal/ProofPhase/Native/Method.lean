/-
Native proof optimization as a dynamics: quantized cost, the gap, and where a contraction exists (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/NATIVE-METHOD.md`, sections 2 and 3.
-/

import Mathlib

/-!
# Optimization passes as a dynamics on proofs

A pass maps a proof to a proof with the same statement. Its cost measures (lemma count, layer count, term size, kernel
steps) are natural numbers: **quantized**. Three results say what that buys, and one says what it does not.

**1. Quantized strict decrease terminates (the gap).** If a pass strictly lowers a natural-number measure whenever it
changes anything (`f x ≠ x → μ (f x) < μ x`), then after at most `μ x` passes the proof is a fixed point
(`fixed_after`). This is a **sign** statement with no rate: each strict decrease is at least one quantum, which is the
whole gap.

**2. A quantized contraction terminates in logarithmically many passes.** If a pass halves the excess over a floor
`m` (`2 (μ (f x) − m) ≤ μ x − m`), the floor is reached after `log₂ (μ x − m) + 1` passes (`reaches_floor`). This is the
Dobrushin pattern of `Mixing/Glauber.lean` (factor `α = 1/2`) with quantized values, which turns "converges" into
"arrives".

**3. Without quanta, strict decrease (even contraction) never arrives.** `x ↦ (x + 1)/2` on the reals strictly lowers
`x` from `2` toward `1`, halving the distance each step, and never reaches `1` (`real_never_arrives`). This is the
`Z_tw < Z` situation: a sign, and here even a rate, but no finite arrival.

**4. Pointer jumping: a pass that contracts depth by `1/2` and conserves cost.** A chain of `d` layers, each with a cost,
merged pairwise (`pairUp`) has `⌈d/2⌉` layers (`length_pairUp`), the same total cost (`sum_pairUp`), and each layer
costs at most twice the old maximum (`le_two_mul_of_mem_pairUp`). After `k` passes there are `⌈d/2^k⌉` layers
(`length_iterate_pairUp`), so one layer after `⌈log₂ d⌉` passes (`iterate_clog_pairUp`). **Depth contracts; total
checking work does not.** It is conserved, so a contraction for the work itself would need passes that remove work,
not merely regroup it.

**New here:** everything in this file.
-/

namespace ProofPhase.Native

/-! ### 1. The gap: quantized strict decrease terminates -/

theorem fixed_after_aux {X : Type*} (f : X → X) (μ : X → ℕ) (h : ∀ x, f x ≠ x → μ (f x) < μ x) :
    ∀ n x, μ x ≤ n → f (f^[n] x) = f^[n] x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    by_contra hne
    have := h x hne
    omega
  | succ n ih =>
    intro x hx
    by_cases hfx : f x = x
    · rw [Function.iterate_fixed hfx]
      exact hfx
    · have := h x hfx
      rw [Function.iterate_succ_apply]
      exact ih (f x) (by omega)

/-- **Quantized strict decrease terminates.** A pass that strictly lowers a natural-number measure whenever it changes
the proof reaches a fixed point after at most `μ x` passes. -/
theorem fixed_after {X : Type*} (f : X → X) (μ : X → ℕ) (h : ∀ x, f x ≠ x → μ (f x) < μ x) (x : X) :
    f (f^[μ x] x) = f^[μ x] x :=
  fixed_after_aux f μ h (μ x) x le_rfl

/-! ### 2. A quantized contraction arrives in logarithmically many passes -/

theorem excess_iterate_le {X : Type*} (f : X → X) (μ : X → ℕ) (m : ℕ)
    (hc : ∀ x, 2 * (μ (f x) - m) ≤ μ x - m) (x : X) (k : ℕ) : 2 ^ k * (μ (f^[k] x) - m) ≤ μ x - m := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, pow_succ]
    have h1 := ih (f x)
    have h2 := hc x
    calc 2 ^ k * 2 * (μ (f^[k] (f x)) - m) = 2 * (2 ^ k * (μ (f^[k] (f x)) - m)) := by ring
      _ ≤ 2 * (μ (f x) - m) := by omega
      _ ≤ μ x - m := h2

/-- **A quantized contraction reaches its floor.** If each pass at least halves the excess of a natural-number measure
over its floor `m`, the floor is reached after `log₂ (μ x − m) + 1` passes. -/
theorem reaches_floor {X : Type*} (f : X → X) (μ : X → ℕ) (m : ℕ) (hm : ∀ x, m ≤ μ x)
    (hc : ∀ x, 2 * (μ (f x) - m) ≤ μ x - m) (x : X) : μ (f^[Nat.log 2 (μ x - m) + 1] x) = m := by
  have h := excess_iterate_le f μ m hc x (Nat.log 2 (μ x - m) + 1)
  have hlt : μ x - m < 2 ^ (Nat.log 2 (μ x - m) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h0 : μ (f^[Nat.log 2 (μ x - m) + 1] x) - m = 0 := by
    by_contra hne
    have : 2 ^ (Nat.log 2 (μ x - m) + 1) ≤ 2 ^ (Nat.log 2 (μ x - m) + 1) * (μ (f^[Nat.log 2 (μ x - m) + 1] x) - m) :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
    omega
  have := hm (f^[Nat.log 2 (μ x - m) + 1] x)
  omega

/-! ### 3. Without quanta: a contraction that never arrives -/

theorem real_iterate (n : ℕ) : (fun x : ℝ => (x + 1) / 2)^[n] 2 = 1 + (1 / 2) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ]
    ring

/-- **The real-valued halving never arrives.** `x ↦ (x + 1)/2` from `2` strictly decreases, halves the distance to `1`
each step, and never reaches `1`. -/
theorem real_never_arrives (n : ℕ) : (fun x : ℝ => (x + 1) / 2)^[n] 2 ≠ 1 ∧
    (fun x : ℝ => (x + 1) / 2)^[n + 1] 2 < (fun x : ℝ => (x + 1) / 2)^[n] 2 := by
  rw [real_iterate, real_iterate, pow_succ]
  have hp : (0 : ℝ) < (1 / 2) ^ n := by positivity
  constructor
  · intro h; linarith
  · linarith

/-! ### 4. Pointer jumping: depth contracts by one half, cost is conserved -/

/-- Merge adjacent layers pairwise. -/
def pairUp {β : Type*} (op : β → β → β) : List β → List β
  | a :: b :: t => op a b :: pairUp op t
  | l => l

theorem length_pairUp {β : Type*} (op : β → β → β) : ∀ l : List β, (pairUp op l).length = (l.length + 1) / 2
  | [] => by simp [pairUp]
  | [_] => by simp [pairUp]
  | a :: b :: t => by
    rw [pairUp, List.length_cons, length_pairUp op t, List.length_cons, List.length_cons]
    omega

/-- **Total cost is conserved** when the cost of a merged layer is the sum of the costs. -/
theorem sum_pairUp {β : Type*} (op : β → β → β) (cost : β → ℕ) (hop : ∀ a b, cost (op a b) = cost a + cost b) :
    ∀ l : List β, ((pairUp op l).map cost).sum = (l.map cost).sum
  | [] => by simp [pairUp]
  | [_] => by simp [pairUp]
  | a :: b :: t => by
    rw [pairUp, List.map_cons, List.sum_cons, sum_pairUp op cost hop t, hop]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- **Each merged layer costs at most twice the old maximum.** -/
theorem le_two_mul_of_mem_pairUp {β : Type*} (op : β → β → β) (cost : β → ℕ)
    (hop : ∀ a b, cost (op a b) = cost a + cost b) {M : ℕ} :
    ∀ l : List β, (∀ x ∈ l, cost x ≤ M) → ∀ y ∈ pairUp op l, cost y ≤ 2 * M
  | [] => fun _ y hy => by simp [pairUp] at hy
  | [a] => fun h y hy => by
    simp only [pairUp, List.mem_singleton] at hy
    subst hy
    have := h _ (List.mem_singleton_self _)
    omega
  | a :: b :: t => fun h y hy => by
    rw [pairUp, List.mem_cons] at hy
    rcases hy with rfl | hy
    · rw [hop]
      have h1 := h a (by simp)
      have h2 := h b (by simp)
      omega
    · exact le_two_mul_of_mem_pairUp op cost hop t (fun x hx => h x (by simp [hx])) y hy

theorem ceil_half_step (n a : ℕ) (ha : 0 < a) : ((n + a - 1) / a + 1) / 2 = (n + 2 * a - 1) / (2 * a) := by
  have h1 : (n + a - 1) / a + 1 = (n + a - 1 + a) / a := (Nat.add_div_right _ ha).symm
  rw [h1, Nat.div_div_eq_div_mul, mul_comm a 2]
  congr 1
  omega

/-- **Depth after `k` passes**: `⌈d / 2^k⌉`. -/
theorem length_iterate_pairUp {β : Type*} (op : β → β → β) (l : List β) (k : ℕ) :
    ((pairUp op)^[k] l).length = (l.length + 2 ^ k - 1) / 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', length_pairUp, ih, ceil_half_step _ _ (by positivity), pow_succ, mul_comm]

/-- **One layer after `⌈log₂ d⌉` passes.** -/
theorem iterate_clog_pairUp {β : Type*} (op : β → β → β) (l : List β) :
    ((pairUp op)^[Nat.clog 2 l.length] l).length ≤ 1 := by
  rw [length_iterate_pairUp]
  have hle : l.length ≤ 2 ^ Nat.clog 2 l.length := Nat.le_pow_clog (by norm_num) _
  have hpos : 0 < 2 ^ Nat.clog 2 l.length := by positivity
  have : (l.length + 2 ^ Nat.clog 2 l.length - 1) / 2 ^ Nat.clog 2 l.length < 2 :=
    (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
  omega

end ProofPhase.Native
