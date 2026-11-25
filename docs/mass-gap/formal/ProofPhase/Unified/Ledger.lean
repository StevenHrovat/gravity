/-
The unified lossy-step theorem: the general part (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/UNIFIED.md`, design `docs/unified/DESIGN.md`.
-/

import Mathlib

/-!
# The certificate ledger: lossy steps, their costs, and a universal floor

**The structure.** A chain of steps `i = 0, 1, ...`. At each step some real numbers are *certified*
(`Cert i e`: an upper bound of an influence, a lower bound of a margin, a bound on a count). Each step carries every
certified value `e` to the certified value `f i * e`. The factor `f i ≥ 0` is the price of the step: a step may shrink a
certificate, never flip its sign. Writing `f i = e^{δ - c i}`, `c i` is the **cost** of the step and `δ` the **floor**,
the same for every step.

**The general theorem.**
* `carry`: `Cert 0 e` gives `Cert n ((∏_{i<n} f i) * e)`. Everything else is a reading of this line.
* `prod_exp_cost`: `∏ e^{δ - c i} = e^{n δ - Σ c i}`; `exists_cost_iff`: a factor has a real cost iff it is positive.
* **Decay** (upper certificates): `ledger` (`M n ≤ e^{n δ - Σ c} M 0` when every step pays at least its cost up to the
  floor, `Pays`), `decay` (`≤ e^{-n (κ - δ)} M 0` when every cost is at least `κ`), `summable_of_gap` (the sum over `n`
  converges when `κ > δ`): **the gap is cost minus floor**.
* **Size** (the same ledger read backwards, a quantum `φ` at the end): `size`, `size_log`
  (`log M 0 ≥ Σ c - n δ + log φ`).
* **Survival** (lower certificates): `survive` (`M n ≥ (∏ f) M 0` for `f ≥ 0`), `survive_pos`.
* **Additive form**: `accrue` (`G n ≥ G 0 + Σ c - n δ`), and `pays_of_accrue` (`M = e^{-G}` pays).
* **Composition by contraction**: `pays_of_submul`. A weight on a monoid of steps that is submultiplicative up to the
  floor, `w (a * b) ≤ e^δ w a w b`, makes the running products pay.
* **The shape of the open hypotheses**: `CostAboveFloor cost δ` (a uniform cost strictly above the floor) and
  `rate_of_costAboveFloor`.

No problem-specific object occurs here. No axioms beyond the standard ones; nothing is assumed.
-/

open Finset

noncomputable section

namespace ProofPhase.Unified

/-! ### 1. The core: certificates carried along a chain -/

/-- Each step `i < n` carries every certified value `e` to the certified value `f i * e`. -/
def Carries (Cert : ℕ → ℝ → Prop) (f : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i < n, ∀ e, Cert i e → Cert (i + 1) (f i * e)

/-- **The certificate ledger.** A certificate at the start is carried to the start times the product of the step
factors. -/
theorem carry {Cert : ℕ → ℝ → Prop} {f : ℕ → ℝ} {n : ℕ} (h : Carries Cert f n) {e : ℝ} (h0 : Cert 0 e) :
    Cert n ((∏ i ∈ range n, f i) * e) := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have := h n (Nat.lt_succ_self n) _ (ih fun i hi => h i (Nat.lt_succ_of_lt hi))
    rwa [prod_range_succ, mul_comm _ (f n), mul_assoc]

/-- The ledger in costs: the product of the prices `e^{δ - c i}` is `e^{n δ - Σ c i}`. -/
theorem prod_exp_cost (c : ℕ → ℝ) (δ : ℝ) (n : ℕ) :
    ∏ i ∈ range n, Real.exp (δ - c i) = Real.exp (n * δ - ∑ i ∈ range n, c i) := by
  rw [← Real.exp_sum, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]

/-- **The sign is a real cost.** A factor is `e^{-c}` for some real cost `c` iff it is positive. -/
theorem exists_cost_iff (f : ℝ) : (∃ c : ℝ, f = Real.exp (-c)) ↔ 0 < f :=
  ⟨fun ⟨c, hc⟩ => hc ▸ Real.exp_pos _, fun h => ⟨-Real.log f, by rw [neg_neg, Real.exp_log h]⟩⟩

/-- With positive factors the product is `e^{-Σ c}`, `c i = -log f i`. -/
theorem prod_eq_exp_neg_cost {f : ℕ → ℝ} (hf : ∀ i, 0 < f i) (n : ℕ) :
    ∏ i ∈ range n, f i = Real.exp (-∑ i ∈ range n, -Real.log (f i)) := by
  rw [sum_neg_distrib, neg_neg, Real.exp_sum]
  exact prod_congr rfl fun i _ => (Real.exp_log (hf i)).symm

/-! ### 2. Decay: upper certificates -/

/-- **A lossy step**: step `i < n` pays at least the cost `c i`, up to the floor `δ`. -/
def Pays (M c : ℕ → ℝ) (δ : ℝ) (n : ℕ) : Prop := ∀ i < n, M (i + 1) ≤ Real.exp (δ - c i) * M i

theorem carries_of_pays {M c : ℕ → ℝ} {δ : ℝ} {n : ℕ} (h : Pays M c δ n) :
    Carries (fun i e => M i ≤ e) (fun i => Real.exp (δ - c i)) n :=
  fun i hi _ he => (h i hi).trans (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)

/-- **The ledger, decay form**: `M n ≤ e^{n δ - Σ c} M 0`. -/
theorem ledger {M c : ℕ → ℝ} {δ : ℝ} {n : ℕ} (h : Pays M c δ n) :
    M n ≤ Real.exp (n * δ - ∑ i ∈ range n, c i) * M 0 := by
  have := carry (carries_of_pays h) (le_refl (M 0))
  rwa [prod_exp_cost] at this

/-- **Uniform cost**: if every step costs at least `κ`, `M n ≤ e^{-n (κ - δ)} M 0`. -/
theorem decay {M c : ℕ → ℝ} {δ κ : ℝ} {n : ℕ} (h : Pays M c δ n) (hκ : ∀ i < n, κ ≤ c i) (hM0 : 0 ≤ M 0) :
    M n ≤ Real.exp (-(n * (κ - δ))) * M 0 := by
  refine (ledger h).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hM0)
  have : (n : ℝ) * κ ≤ ∑ i ∈ range n, c i := by
    have := card_nsmul_le_sum (range n) c κ fun i hi => hκ i (mem_range.1 hi)
    simpa [nsmul_eq_mul] using this
  linarith

/-- **The gap is cost minus floor**: with every cost `≥ κ > δ` along an infinite chain of nonnegative quantities, the
sum over `n` converges. -/
theorem summable_of_gap {M c : ℕ → ℝ} {δ κ : ℝ} (h : ∀ n, Pays M c δ n) (hκ : ∀ i, κ ≤ c i) (hgap : δ < κ)
    (hM : ∀ n, 0 ≤ M n) : Summable M := by
  have hq : Real.exp (-(κ - δ)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  refine Summable.of_nonneg_of_le hM (fun n => ?_)
    ((summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_right (M 0))
  have := decay (h n) (fun i _ => hκ i) (hM 0)
  rwa [show -((n : ℝ) * (κ - δ)) = n * (-(κ - δ)) by ring, Real.exp_nat_mul] at this

/-! ### 3. Size: the ledger read backwards, with a quantum at the end -/

/-- **Size**: a quantum `φ > 0` left at the end forces `φ e^{Σ c - n δ} ≤ M 0`. -/
theorem size {M c : ℕ → ℝ} {δ φ : ℝ} {n : ℕ} (h : Pays M c δ n) (hφ : φ ≤ M n) :
    φ * Real.exp (∑ i ∈ range n, c i - n * δ) ≤ M 0 := by
  have h1 := hφ.trans (ledger h)
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (∑ i ∈ range n, c i - n * δ)).le
  rwa [mul_comm (Real.exp _) (M 0), mul_assoc, ← Real.exp_add, show (n : ℝ) * δ - ∑ i ∈ range n, c i +
    (∑ i ∈ range n, c i - n * δ) = 0 by ring, Real.exp_zero, mul_one] at h2

/-- **Size, additive form**: the global quantity `log M 0` is at least the sum of the costs minus the floor. -/
theorem size_log {M c : ℕ → ℝ} {δ φ : ℝ} {n : ℕ} (h : Pays M c δ n) (hφ0 : 0 < φ) (hφ : φ ≤ M n) :
    ∑ i ∈ range n, c i - n * δ + Real.log φ ≤ Real.log (M 0) := by
  have hs := size h hφ
  have hpos : 0 < φ * Real.exp (∑ i ∈ range n, c i - n * δ) := mul_pos hφ0 (Real.exp_pos _)
  have := Real.log_le_log hpos hs
  rwa [Real.log_mul hφ0.ne' (Real.exp_pos _).ne', Real.log_exp, add_comm] at this

/-! ### 4. Survival: lower certificates -/

/-- **Survival**: steps that keep at least the share `f i ≥ 0` give `M n ≥ (∏ f) M 0`. -/
theorem survive {M f : ℕ → ℝ} {n : ℕ} (hf : ∀ i < n, 0 ≤ f i) (h : ∀ i < n, f i * M i ≤ M (i + 1)) :
    (∏ i ∈ range n, f i) * M 0 ≤ M n :=
  carry (Cert := fun i e => e ≤ M i) (fun i hi _ he => (mul_le_mul_of_nonneg_left he (hf i hi)).trans (h i hi))
    (le_refl (M 0))

/-- **Survival in costs**: every step paid at a real cost keeps a positive quantity positive,
`M n ≥ e^{-Σ c} M 0 > 0`. -/
theorem survive_pos {M c : ℕ → ℝ} {n : ℕ} (h : ∀ i < n, Real.exp (-c i) * M i ≤ M (i + 1)) (hM0 : 0 < M 0) :
    0 < Real.exp (-∑ i ∈ range n, c i) * M 0 ∧ Real.exp (-∑ i ∈ range n, c i) * M 0 ≤ M n := by
  refine ⟨mul_pos (Real.exp_pos _) hM0, ?_⟩
  have := survive (fun i _ => (Real.exp_pos (-c i)).le) h
  rwa [show (∏ i ∈ range n, Real.exp (-c i)) = Real.exp (-∑ i ∈ range n, c i) by
    rw [← Real.exp_sum, sum_neg_distrib]] at this

/-! ### 5. The additive form -/

/-- Step `i < n` adds at least `c i - δ` to the global quantity `G`. -/
def Accrues (G c : ℕ → ℝ) (δ : ℝ) (n : ℕ) : Prop := ∀ i < n, G i + c i - δ ≤ G (i + 1)

/-- **The additive ledger**: `G n ≥ G 0 + Σ c - n δ`. -/
theorem accrue {G c : ℕ → ℝ} {δ : ℝ} {n : ℕ} (h : Accrues G c δ n) :
    G 0 + ∑ i ∈ range n, c i - n * δ ≤ G n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := h n (Nat.lt_succ_self n)
    have := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
    rw [sum_range_succ]
    push_cast
    linarith

/-- The additive and the multiplicative ledger agree: `M = e^{-G}` pays when `G` accrues. -/
theorem pays_of_accrue {G c : ℕ → ℝ} {δ : ℝ} {n : ℕ} (h : Accrues G c δ n) :
    Pays (fun i => Real.exp (-G i)) c δ n := fun i hi => by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith [h i hi])

/-! ### 6. Composition by contraction -/

/-- The running composite of the steps `s 0, ..., s (n - 1)`. -/
def runProd {S : Type*} [Monoid S] (s : ℕ → S) : ℕ → S
  | 0 => 1
  | n + 1 => runProd s n * s n

/-- **Contractions compose into a lossy chain.** A nonnegative weight, submultiplicative up to the floor, on steps of
weight at most `e^{-c i}`: the running composites pay the costs up to the floor. -/
theorem pays_of_submul {S : Type*} [Monoid S] (w : S → ℝ) (hw : ∀ a, 0 ≤ w a) {δ : ℝ}
    (hsub : ∀ a b, w (a * b) ≤ Real.exp δ * w a * w b) (s : ℕ → S) (c : ℕ → ℝ) (hs : ∀ i, w (s i) ≤ Real.exp (-c i))
    (n : ℕ) : Pays (fun i => w (runProd s i)) c δ n := fun i _ => by
  show w (runProd s i * s i) ≤ _
  calc w (runProd s i * s i) ≤ Real.exp δ * w (runProd s i) * w (s i) := hsub _ _
    _ ≤ Real.exp δ * w (runProd s i) * Real.exp (-c i) :=
        mul_le_mul_of_nonneg_left (hs i) (mul_nonneg (Real.exp_pos _).le (hw _))
    _ = Real.exp (δ - c i) * w (runProd s i) := by
        rw [sub_eq_add_neg, Real.exp_add]; ring

/-! ### 7. The shape of the open hypotheses -/

/-- **Cost above floor**: a uniform cost `κ`, strictly above the floor `δ`, paid everywhere (at every step, for every
outside). -/
def CostAboveFloor {Ω : Type*} (cost : Ω → ℝ) (δ : ℝ) : Prop := ∃ κ : ℝ, δ < κ ∧ ∀ ω, κ ≤ cost ω

/-- Cost above floor gives a positive rate: an infinite chain whose steps pay a cost of that kind decays at rate
`κ - δ > 0` and is summable. -/
theorem rate_of_costAboveFloor {Ω : Type*} {cost : Ω → ℝ} {δ : ℝ} (hc : CostAboveFloor cost δ) {M : ℕ → ℝ}
    (ω : ℕ → Ω) (h : ∀ n, Pays M (fun i => cost (ω i)) δ n) (hM : ∀ n, 0 ≤ M n) :
    ∃ κ : ℝ, δ < κ ∧ (∀ n, M n ≤ Real.exp (-(n * (κ - δ))) * M 0) ∧ Summable M := by
  obtain ⟨κ, hκ, hcost⟩ := hc
  exact ⟨κ, hκ, fun n => decay (h n) (fun i _ => hcost (ω i)) (hM 0),
    summable_of_gap h (fun i => hcost (ω i)) hκ hM⟩

end ProofPhase.Unified
