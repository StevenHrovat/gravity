/-
Uniformity along the chain, part 2: submultiplicativity and the homogeneous chain (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/CHAIN.md`.
-/

import ProofPhase.Mixing.Doeblin

/-!
# Contraction coefficients multiply along a chain

Kernels are stochastic matrices (`IsStoch`, `Doeblin.lean`); `kcomp K L` is the composite "first `K`, then `L`"
(matrix product) and `pushv a K` is the law of the output when the input has law `a`.

* `tv_pushv_le`: if `Contracts L θ`, then for any two probability vectors `a b`,
  `tv (pushv a L) (pushv b L) ≤ θ * tv a b`. Proof: couple `a` and `b` maximally (`maxCoup`, `Classical.lean`); the two
  outputs differ only where the coupled inputs differ, and there they are at distance at most `θ`.
* `contracts_kcomp`: **submultiplicativity**. `Contracts K η` and `Contracts L θ` give `Contracts (kcomp K L) (η * θ)`.
* `contracts_kchain`: kernels `K_0, ..., K_{n-1}` with coefficients `≤ η_i` compose to coefficient `≤ ∏ η_i`.
* `contracts_kpow`: the same kernel applied `n` times (the same transfer step at every block) has coefficient `≤ η ^ n`.
* `tv_pushv_kpow_le`: influence across `n` blocks. Two different inputs have outputs at distance `≤ η ^ n`.
* `contracts_kpow_of_doeblin`: with a floor `K x y ≥ ε ν y`, the coefficient of `K ^ n` is at most `(1 - ε) ^ n`.

The last section is the honest limit, as a note and two small lemmas: a bound `1 - e^{-C}` per channel gives a Dobrushin
column sum `k (1 - e^{-C})` over `k` neighbouring channels, and that is `≥ 1` as soon as `k ≥ 2` and `C ≥ log 2`.

No axioms beyond the standard ones; nothing is assumed.
-/

open Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Mixing

section Push

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- The law of the output of the kernel `K` when the input has law `a`. -/
def pushv (a : X → ℝ) (K : X → Y → ℝ) : Y → ℝ := fun y => ∑ x, a x * K x y

/-- Composite of two kernels: first `K`, then `L`. -/
def kcomp (K : X → Y → ℝ) (L : Y → Z → ℝ) : X → Z → ℝ := fun x z => ∑ y, K x y * L y z

theorem kcomp_row (K : X → Y → ℝ) (L : Y → Z → ℝ) (x : X) : kcomp K L x = pushv (K x) L := rfl

theorem pushv_kcomp (a : X → ℝ) (K : X → Y → ℝ) (L : Y → Z → ℝ) :
    pushv a (kcomp K L) = pushv (pushv a K) L := by
  funext z
  simp only [pushv, kcomp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

theorem isStoch_kcomp {K : X → Y → ℝ} {L : Y → Z → ℝ} (hK : IsStoch K) (hL : IsStoch L) :
    IsStoch (kcomp K L) := by
  refine ⟨fun x z => Finset.sum_nonneg fun y _ => mul_nonneg (hK.nonneg x y) (hL.nonneg y z), fun x => ?_⟩
  simp only [kcomp]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hL.sum_one, mul_one]
  exact hK.sum_one x

/-- A coupling `c` of `a` and `b`, with a kernel `K` of contraction coefficient `θ`: the outputs are at distance at
most `θ` times the mass `c` puts off the diagonal. -/
theorem tv_pushv_le_coupling {a b : X → ℝ} (c : X → X → ℝ) (hc0 : ∀ s t, 0 ≤ c s t)
    (hcR : ∀ s, ∑ t, c s t = a s) (hcL : ∀ t, ∑ s, c s t = b t) {K : X → Y → ℝ} {θ : ℝ}
    (hK : Contracts K θ) :
    tv (pushv a K) (pushv b K) ≤ θ * ∑ s, ∑ t, (if s = t then 0 else c s t) := by
  have h1 : ∀ y, pushv a K y - pushv b K y = ∑ s, ∑ t, c s t * (K s y - K t y) := by
    intro y
    have e1 : pushv a K y = ∑ s, ∑ t, c s t * K s y := by
      unfold pushv
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← hcR s, Finset.sum_mul]
    have e2 : pushv b K y = ∑ s, ∑ t, c s t * K t y := by
      unfold pushv
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← hcL t, Finset.sum_mul]
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hterm : ∀ s t, c s t * tv (K s) (K t) ≤ θ * (if s = t then 0 else c s t) := by
    intro s t
    by_cases h : s = t
    · subst h; simp [tv_self]
    · simp only [h, ↓reduceIte]
      calc c s t * tv (K s) (K t) ≤ c s t * θ := mul_le_mul_of_nonneg_left (hK s t) (hc0 s t)
        _ = θ * c s t := mul_comm _ _
  have hy : ∀ y, |pushv a K y - pushv b K y| ≤ ∑ s, ∑ t, c s t * |K s y - K t y| := by
    intro y
    rw [h1 y]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [abs_mul, abs_of_nonneg (hc0 s t)]
  have h2 : ∑ y, |pushv a K y - pushv b K y| ≤ ∑ s, ∑ t, c s t * (2 * tv (K s) (K t)) := by
    calc ∑ y, |pushv a K y - pushv b K y| ≤ ∑ y, ∑ s, ∑ t, c s t * |K s y - K t y| :=
          Finset.sum_le_sum fun y _ => hy y
      _ = ∑ s, ∑ t, c s t * ∑ y, |K s y - K t y| := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ s, ∑ t, c s t * (2 * tv (K s) (K t)) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
          unfold tv; ring
  have h5 : ∑ s, ∑ t, c s t * (2 * tv (K s) (K t)) = 2 * ∑ s, ∑ t, c s t * tv (K s) (K t) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
  have h6 : θ * ∑ s, ∑ t, (if s = t then (0 : ℝ) else c s t) =
      ∑ s, ∑ t, θ * (if s = t then 0 else c s t) := by
    simp only [Finset.mul_sum]
  have h7 := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) =>
    Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hterm s t
  rw [h6]
  unfold tv
  linarith [h2, h5, h7]

/-- **A kernel with coefficient `θ` contracts total variation by `θ`.** -/
theorem tv_pushv_le {a b : X → ℝ} (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (ha1 : ∑ x, a x = 1)
    (hb1 : ∑ x, b x = 1) {K : X → Y → ℝ} {θ : ℝ} (hK : Contracts K θ) :
    tv (pushv a K) (pushv b K) ≤ θ * tv a b := by
  obtain ⟨x0⟩ : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at ha1
  have hθ : 0 ≤ θ := (tv_self (K x0)).symm.le.trans (hK x0 x0)
  refine (tv_pushv_le_coupling (maxCoup a b) (maxCoup_nonneg ha hb ha1) (maxCoup_sum_right ha1 hb1)
    (maxCoup_sum_left ha1 hb1) hK).trans (mul_le_mul_of_nonneg_left ?_ hθ)
  rw [← dlt_eq_tv ha1 hb1]
  exact maxCoup_offdiag_le ha1 hb1

/-- **Submultiplicativity.** The composite of a kernel with coefficient `≤ η` and one with coefficient `≤ θ` has
coefficient `≤ η * θ`. -/
theorem contracts_kcomp {K : X → Y → ℝ} {L : Y → Z → ℝ} {η θ : ℝ} (hK : IsStoch K) (hKη : Contracts K η)
    (hLθ : Contracts L θ) : Contracts (kcomp K L) (η * θ) := by
  intro x x'
  obtain ⟨y0⟩ : Nonempty Y := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hK.sum_one x
    simp at this
  have hθ : 0 ≤ θ := (tv_self (L y0)).symm.le.trans (hLθ y0 y0)
  rw [kcomp_row, kcomp_row]
  calc tv (pushv (K x) L) (pushv (K x') L) ≤ θ * tv (K x) (K x') :=
        tv_pushv_le (hK.nonneg x) (hK.nonneg x') (hK.sum_one x) (hK.sum_one x') hLθ
    _ ≤ θ * η := mul_le_mul_of_nonneg_left (hKη x x') hθ
    _ = η * θ := mul_comm _ _

end Push

section Chain

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The identity kernel (no step). -/
def idK (X : Type*) [DecidableEq X] : X → X → ℝ := fun x y => if x = y then 1 else 0

theorem isStoch_idK : IsStoch (idK X) :=
  ⟨fun x y => by unfold idK; split_ifs <;> norm_num, fun x => by simp [idK]⟩

/-- The chain `K_{n-1}` after ... after `K_0`: `kchain Ks n = K_0 ; K_1 ; ... ; K_{n-1}` (one kernel per block). -/
def kchain (Ks : ℕ → X → X → ℝ) : ℕ → X → X → ℝ
  | 0 => idK X
  | n + 1 => kcomp (kchain Ks n) (Ks n)

/-- The same kernel at every step: `K ^ n`. -/
def kpow (K : X → X → ℝ) (n : ℕ) : X → X → ℝ := kchain (fun _ => K) n

theorem isStoch_kchain {Ks : ℕ → X → X → ℝ} (h : ∀ i, IsStoch (Ks i)) (n : ℕ) : IsStoch (kchain Ks n) := by
  induction n with
  | zero => exact isStoch_idK
  | succ n ih => exact isStoch_kcomp ih (h n)

/-- **Contraction coefficients multiply along a chain of different kernels.** -/
theorem contracts_kchain {Ks : ℕ → X → X → ℝ} {η : ℕ → ℝ} (hs : ∀ i, IsStoch (Ks i))
    (hc : ∀ i, Contracts (Ks i) (η i)) (n : ℕ) : Contracts (kchain Ks n) (∏ i ∈ Finset.range n, η i) := by
  induction n with
  | zero => simpa [kchain] using isStoch_idK.contracts_one
  | succ n ih =>
    rw [Finset.prod_range_succ]
    exact contracts_kcomp (isStoch_kchain hs n) ih (hc n)

/-- **Homogeneous chain.** The same transfer step `K` at every block, coefficient `≤ η`: `K ^ n` has coefficient
`≤ η ^ n`. -/
theorem contracts_kpow {K : X → X → ℝ} {η : ℝ} (hK : IsStoch K) (hη : Contracts K η) (n : ℕ) :
    Contracts (kpow K n) (η ^ n) := by
  have h := contracts_kchain (Ks := fun _ => K) (η := fun _ => η) (fun _ => hK) (fun _ => hη) n
  simpa [kpow, Finset.prod_const] using h

theorem isStoch_kpow {K : X → X → ℝ} (hK : IsStoch K) (n : ℕ) : IsStoch (kpow K n) :=
  isStoch_kchain (fun _ => hK) n

/-- **Influence across `n` blocks decays like `η ^ n`.** Two inputs `a`, `b` (probability vectors) give outputs of the
`n`-fold homogeneous chain at total-variation distance at most `η ^ n * tv a b ≤ η ^ n`. -/
theorem tv_pushv_kpow_le {K : X → X → ℝ} {η : ℝ} (hK : IsStoch K) (hη : Contracts K η) {a b : X → ℝ}
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (ha1 : ∑ x, a x = 1) (hb1 : ∑ x, b x = 1) (n : ℕ) :
    tv (pushv a (kpow K n)) (pushv b (kpow K n)) ≤ η ^ n * tv a b :=
  tv_pushv_le ha hb ha1 hb1 (contracts_kpow hK hη n)

theorem tv_pushv_kpow_le_pow {K : X → X → ℝ} {η : ℝ} (hK : IsStoch K) (hη : Contracts K η) {a b : X → ℝ}
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (ha1 : ∑ x, a x = 1) (hb1 : ∑ x, b x = 1) (n : ℕ) :
    tv (pushv a (kpow K n)) (pushv b (kpow K n)) ≤ η ^ n := by
  have h0 : 0 ≤ η := by
    obtain ⟨x0⟩ : Nonempty X := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at ha1
    exact (tv_self (K x0)).symm.le.trans (hη x0 x0)
  calc _ ≤ η ^ n * tv a b := tv_pushv_kpow_le hK hη ha hb ha1 hb1 n
    _ ≤ η ^ n * 1 := mul_le_mul_of_nonneg_left (tv_le_one ha hb ha1 hb1) (pow_nonneg h0 n)
    _ = η ^ n := mul_one _

/-- The step law of the homogeneous chain: one more block is one more application of `K`. -/
theorem pushv_kpow_succ (a : X → ℝ) (K : X → X → ℝ) (n : ℕ) :
    pushv a (kpow K (n + 1)) = pushv (pushv a (kpow K n)) K :=
  pushv_kcomp a (kpow K n) K

/-- **Doeblin, iterated.** A floor `K x y ≥ ε ν y` makes the `n`-fold chain contract by `(1 - ε) ^ n`. -/
theorem contracts_kpow_of_doeblin {K : X → X → ℝ} (hK : IsStoch K) {ν : X → ℝ} (hν : ∑ y, ν y = 1) {ε : ℝ}
    (hε : ∀ x y, ε * ν y ≤ K x y) (n : ℕ) : Contracts (kpow K n) ((1 - ε) ^ n) :=
  contracts_kpow hK (contracts_of_doeblin hK hν hε) n

end Chain

/-! ### The honest limit: a bound per channel does not sum

NOTE. The influence of a box on its neighbours is bounded by the contraction coefficient of each neighbouring channel.
Dobrushin's condition needs the *sum* of the influences over all neighbouring channels (a column of the influence matrix)
to be below `1`, not each channel. With `k` neighbouring channels of coefficients `η_1, ..., η_k` the column sum is
`η_1 + ... + η_k`. The Doeblin floor gives `η_i ≤ 1 - e^{-C}` per channel (`box_bound`), and that bound cannot be improved
from the floor alone (`doeblin_sharp`). The sum of these bounds is `k (1 - e^{-C})`, and it is below `1` only when
`C < log (k / (k - 1))`; for `k ≥ 2` and `C ≥ log 2` it is at least `1` (`column_sum_ge_one`), so the per-channel Doeblin
bound by itself never gives a column sum below `1` there. What is needed in addition: a summed bound over the channels
(a floor for the joint kernel of all channels, or an influence estimate that gets smaller with the number of channels).
-/

section Channels

/-- The sum of `k` per-channel bounds is at most `k (1 - e^{-C})`. -/
theorem column_sum_le {k : ℕ} {C : ℝ} {η : Fin k → ℝ} (h : ∀ i, η i ≤ 1 - Real.exp (-C)) :
    ∑ i, η i ≤ k * (1 - Real.exp (-C)) := by
  calc ∑ i, η i ≤ ∑ _i : Fin k, (1 - Real.exp (-C)) := Finset.sum_le_sum fun i _ => h i
    _ = k * (1 - Real.exp (-C)) := by simp; ring

/-- **The honest limit.** With `k ≥ 2` neighbouring channels and `C ≥ log 2`, the sum of the per-channel Doeblin
bounds `1 - e^{-C}` is at least `1`: it does not give a column sum below `1`. -/
theorem column_sum_ge_one {k : ℕ} (hk : 2 ≤ k) {C : ℝ} (hC : Real.log 2 ≤ C) :
    1 ≤ k * (1 - Real.exp (-C)) := by
  have h1 : Real.exp (-C) ≤ 1 / 2 := by
    have : Real.exp (-C) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    linarith
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- The sharp threshold: for `k ≥ 1`, `k (1 - e^{-C}) < 1` exactly when `1 - 1/k < e^{-C}`. -/
theorem column_sum_lt_one_iff {k : ℕ} (hk : 1 ≤ k) {C : ℝ} :
    (k : ℝ) * (1 - Real.exp (-C)) < 1 ↔ 1 - 1 / (k : ℝ) < Real.exp (-C) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h : (k : ℝ) * (1 - Real.exp (-C)) < 1 ↔ 1 - Real.exp (-C) < 1 / k := by
    rw [lt_div_iff₀ hk', mul_comm]
  rw [h]
  constructor <;> intro h' <;> linarith

end Channels

end ProofPhase.Mixing
