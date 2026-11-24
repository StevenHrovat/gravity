/-
The Existence Turing Machine round: the machine, and the exact edge of its halting claim (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/ETM.md`.
-/

import ProofPhase.ETM.RunSys
import ProofPhase.Unified.Encoder

/-!
# The Existence Turing Machine: universality, halting on the contraction class, and Turing's limit

**(a) Universality (`etm`, `etm_runs`, `etm_universal`).** One running system, the ETM, runs every described content.
* *Describes*: a description is a program `c : Nat.Partrec.Code` (Mathlib's Kleene codes, Goedel-numbered) and an input
  `n : ℕ`; the start state is `start c n`.
* *Runs*: a state is `((k, c), n)` with `k` the fuel spent; the step adds one unit of fuel; the mass is `1` while the
  bounded evaluation `evaln k c n` has no value and `0` once it has one (balance); the factor is `1` and the floor `0`.
  The ETM reaches balance from `start c n` exactly when `c` halts on `n` (`etm_runs`), and the value it reads off is the
  value of `c` on `n` (`etm_output`, `etm_output_complete`).
* Every partial recursive function is run this way by some description (`etm_universal`, from Mathlib's
  `Nat.Partrec.Code.exists_code`). The step and the balance test are primitive recursive (`estep_primrec`,
  `halted_primrec`, from `Nat.Partrec.Code.primrec_evaln`).

**(b) Halting on the contraction class (`Contracting`, `reaches_of_contracting`).** A running system is in the
contraction class when every factor is at most `θ` with `e^δ θ < 1`; with positive factors this is exactly a cost above
the floor (`contracting_iff_costAboveFloor`). On that class, from any state of mass at most `M`, the mass is at most `ε`
at every step `n ≥ balanceBound M ε q` (any rational `q ≥ e^δ θ`, `q < 1`), with the explicit, computable bound
`balanceBound M ε q = ⌈M q / (ε (1 − q))⌉₊ + 1` (`balanceBound`, a Lean `def` on rationals, evaluated by the kernel in
`balanceBound_example`). So "reaches balance within `ε`" is decided on the class: it always holds, and the unbounded
search is equivalent to a search below the bound (`reaches_iff_bounded`). Content that keeps mass above `ε` forever is
not in the class (`not_contracting_of_persists`).

**(c) Binary global truth, no global procedure.** (c1) For every content, "the ETM reaches balance" has a truth value,
a total `Bool` by classical decidability (`etmTruth`, `etmTruth_spec`, `etm_binary`); the definition is `noncomputable`.
(c2) No computable predicate decides it for all descriptions (`etm_balance_undecidable`, Mathlib's
`ComputablePred.halting_problem`), so the truth function is not computable (`etmTruth_not_computable`,
`etm_truth_edge`). The ETM itself is lossless, factor `1`, cost `0` = floor, so it is outside the contraction class
(`etm_not_contracting`).

**The edge (`etm_edge`).** Cost above the floor: halting decided, with an explicit bound. Cost equal to the floor
(lossless): Turing-universal, halting undecidable. (b) and (c) together are the exact edge of the ETM claim.

No axioms beyond the standard ones.
-/

open Finset Nat.Partrec Nat.Partrec.Code

noncomputable section

namespace ProofPhase.ETM

universe u

namespace RunSys

variable {δ : ℝ}

/-- The run from `x` is within `ε` of balance at step `n`. -/
def Balanced (S : RunSys.{u} δ) (ε : ℝ) (x : S.X) (n : ℕ) : Prop := S.mass (S.step^[n] x) ≤ ε

/-- The run from `x` reaches balance within `ε`. -/
def Reaches (S : RunSys.{u} δ) (ε : ℝ) (x : S.X) : Prop := ∃ n, S.Balanced ε x n

/-- **The contraction class**: every encoder factor at most `θ`, with `e^δ θ < 1` (a cost above the floor). -/
def Contracting (S : RunSys.{u} δ) (θ : ℝ) : Prop := (∀ x, S.fac x ≤ θ) ∧ Real.exp δ * θ < 1

/-- **The contraction class is the class of costs above the floor** (positive factors, cost `−log fac`). -/
theorem contracting_iff_costAboveFloor (S : RunSys.{u} δ) (hf : ∀ x, 0 < S.fac x) :
    (∃ θ, S.Contracting θ) ↔ ProofPhase.Unified.CostAboveFloor (fun x => -Real.log (S.fac x)) δ := by
  have hed : Real.exp δ * Real.exp (-δ) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  constructor
  · rintro ⟨θ, hθ, hq⟩
    have hθ' : θ < Real.exp (-δ) := by
      have h := mul_lt_mul_of_pos_left hq (Real.exp_pos (-δ))
      rwa [mul_one, ← mul_assoc, mul_comm (Real.exp (-δ)), hed, one_mul] at h
    refine ProofPhase.Unified.costAboveFloor_of_factor_le hf (r := max θ (Real.exp (-δ) / 2))
      (lt_max_of_lt_right (by positivity)) (fun x => (hθ x).trans (le_max_left _ _)) (max_lt hθ' ?_)
    linarith [Real.exp_pos (-δ)]
  · intro h
    obtain ⟨r, _, hrδ, hr⟩ := ProofPhase.Unified.factor_le_of_costAboveFloor hf h
    refine ⟨r, hr, ?_⟩
    have := mul_lt_mul_of_pos_left hrδ (Real.exp_pos δ)
    rwa [hed] at this

end RunSys

/-! ## (b) Halting on the contraction class -/

/-- `n q^n (1 − q) ≤ q (1 − q^n)` on `[0, 1]`: the elementary estimate behind the explicit bound. -/
theorem nat_mul_pow_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    (n : ℝ) * q ^ n * (1 - q) ≤ q * (1 - q ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := mul_le_mul_of_nonneg_left ih hq0
    have h2 : q ^ (n + 1) ≤ q := pow_le_of_le_one hq0 hq1 (Nat.succ_ne_zero n)
    have h3 : 0 ≤ (q - q ^ (n + 1)) * (1 - q) := mul_nonneg (by linarith) (by linarith)
    push_cast
    rw [pow_succ] at h2 h3 ⊢
    nlinarith [h1, h3]

/-- **Geometric decay below `ε` after an explicit number of steps**: `M q^n ≤ ε` once `n ≥ 1` and
`n ≥ M q / (ε (1 − q))`. -/
theorem geom_le (M ε q : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) (hn1 : 1 ≤ n)
    (hn : M * q / (ε * (1 - q)) ≤ n) : M * q ^ n ≤ ε := by
  have hd : 0 < ε * (1 - q) := mul_pos hε (by linarith)
  have hnq : 0 < (n : ℝ) * (1 - q) := mul_pos (by exact_mod_cast hn1) (by linarith)
  have A := mul_le_mul_of_nonneg_left (nat_mul_pow_le q hq0 hq1.le n) hM
  have B : 0 ≤ M * q * q ^ n := mul_nonneg (mul_nonneg hM hq0) (pow_nonneg hq0 n)
  have C : M * q ≤ n * (ε * (1 - q)) := (div_le_iff₀ hd).1 hn
  have key : (M * q ^ n) * ((n : ℝ) * (1 - q)) ≤ ε * ((n : ℝ) * (1 - q)) := by nlinarith [A, B, C]
  exact le_of_mul_le_mul_right key hnq

/-- **The explicit, computable step bound** `⌈M q / (ε (1 − q))⌉₊ + 1`, on rational data. -/
def balanceBound (M ε q : ℚ) : ℕ := ⌈M * q / (ε * (1 - q))⌉₊ + 1

/-- The bound is evaluated by the kernel: mass `1`, ratio `1/2`, tolerance `1/1000`: `1001` steps. -/
theorem balanceBound_example : balanceBound 1 (1 / 1000) (1 / 2) = 1001 := by norm_num [balanceBound]

theorem balanceBound_ge (M ε q : ℚ) :
    1 ≤ balanceBound M ε q ∧ (M : ℝ) * q / (ε * (1 - q)) ≤ (balanceBound M ε q : ℝ) := by
  refine ⟨Nat.le_add_left 1 _, ?_⟩
  have h := Nat.le_ceil (M * q / (ε * (1 - q)))
  have h' : ((M * q / (ε * (1 - q)) : ℚ) : ℝ) ≤ ((⌈M * q / (ε * (1 - q))⌉₊ : ℚ) : ℝ) := Rat.cast_le.2 h
  push_cast at h'
  unfold balanceBound
  push_cast
  linarith

namespace RunSys

variable {δ : ℝ}

/-- **Halting on the contraction class, with an explicit computable bound.** In the contraction class, from a state of
mass at most `M`, the run is within `ε` of balance at every step `n ≥ balanceBound M ε q`, for any rational `q` with
`e^δ θ ≤ q < 1`. -/
theorem reaches_of_contracting (S : RunSys.{u} δ) {θ : ℝ} (hS : S.Contracting θ) (x : S.X) {M ε q : ℚ}
    (hq : Real.exp δ * θ ≤ q) (hq1 : q < 1) (hM : S.mass x ≤ M) (hε : 0 < ε) :
    ∀ n ≥ balanceBound M ε q, S.Balanced ε x n := by
  intro n hn
  have hθ0 : 0 ≤ θ := (S.fac_nonneg x).trans (hS.1 x)
  have hq0 : (0 : ℝ) ≤ q := (mul_nonneg (Real.exp_pos δ).le hθ0).trans hq
  have hM0 : (0 : ℝ) ≤ M := (S.mass_nonneg x).trans hM
  have hq1' : (q : ℝ) < 1 := by exact_mod_cast hq1
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨hb1, hb⟩ := balanceBound_ge M ε q
  have hn' : (balanceBound M ε q : ℝ) ≤ n := by exact_mod_cast hn
  have hgeom := geom_le M ε q hM0 hε' hq0 hq1' n (hb1.trans hn) (hb.trans hn')
  unfold Balanced
  calc S.mass (S.step^[n] x) ≤ (Real.exp δ * θ) ^ n * S.mass x := S.contract hS.1 x n
    _ ≤ (q : ℝ) ^ n * M := mul_le_mul (pow_le_pow_left₀ (mul_nonneg (Real.exp_pos δ).le hθ0) hq n) hM
        (S.mass_nonneg x) (pow_nonneg hq0 n)
    _ = M * q ^ n := mul_comm _ _
    _ ≤ ε := hgeom

/-- **On the contraction class the unbounded search is a bounded one**: reaching balance is equivalent to reaching it
below the explicit bound (and both hold). -/
theorem reaches_iff_bounded (S : RunSys.{u} δ) {θ : ℝ} (hS : S.Contracting θ) (x : S.X) {M ε q : ℚ}
    (hq : Real.exp δ * θ ≤ q) (hq1 : q < 1) (hM : S.mass x ≤ M) (hε : 0 < ε) :
    (S.Reaches ε x ↔ ∃ n ≤ balanceBound M ε q, S.Balanced ε x n) ∧ S.Reaches ε x := by
  have h := S.reaches_of_contracting hS x hq hq1 hM hε _ le_rfl
  exact ⟨⟨fun _ => ⟨_, le_rfl, h⟩, fun ⟨n, _, hn⟩ => ⟨n, hn⟩⟩, ⟨_, h⟩⟩

/-- **The contraction class reaches balance from every state** (rational bounds chosen for the real data). -/
theorem reaches_of_contracting' (S : RunSys.{u} δ) {θ : ℝ} (hS : S.Contracting θ) (x : S.X) {ε : ℝ} (hε : 0 < ε) :
    S.Reaches ε x := by
  obtain ⟨q, hq, hq1⟩ := exists_rat_btwn hS.2
  obtain ⟨M, hM⟩ := exists_rat_gt (S.mass x)
  obtain ⟨ε', hε'0, hε'⟩ := exists_rat_btwn hε
  have := S.reaches_of_contracting hS x hq.le (by exact_mod_cast hq1) hM.le (by exact_mod_cast hε'0) _ le_rfl
  exact ⟨_, this.trans hε'.le⟩

/-- **Content that never balances is not in the contraction class.** -/
theorem not_contracting_of_persists (S : RunSys.{u} δ) (x : S.X) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ n, ε < S.mass (S.step^[n] x)) (θ : ℝ) : ¬ S.Contracting θ := fun hS => by
  obtain ⟨n, hn⟩ := S.reaches_of_contracting' hS x hε
  exact absurd hn (not_le.2 (h n))

end RunSys

/-! ## (a) The machine -/

/-- An ETM state `((k, c), n)`: fuel `k` spent, description `c`, input `n`. -/
abbrev EState := (ℕ × Code) × ℕ

/-- One step: one more unit of fuel. -/
def estep (s : EState) : EState := ((s.1.1 + 1, s.1.2), s.2)

/-- The balance test: the bounded evaluation with the fuel spent has a value. -/
def halted (s : EState) : Bool := (evaln s.1.1 s.1.2 s.2).isSome

/-- The start state for description `c` and input `n`. -/
def start (c : Code) (n : ℕ) : EState := ((0, c), n)

theorem halted_mono {s : EState} (h : halted s = true) : halted (estep s) = true := by
  unfold halted estep at *
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
  exact Option.isSome_iff_exists.2 ⟨x, evaln_mono (Nat.le_succ _) hx⟩

/-- **The Existence Turing Machine**: a running system with floor `0`, lossless factor `1`, and mass `1` until the
content's evaluation has a value, `0` from then on. -/
def etm : RunSys.{0} 0 where
  X := EState
  step := estep
  fac _ := 1
  mass s := if halted s then 0 else 1
  fac_nonneg _ := zero_le_one
  fac_le_one _ := le_rfl
  mass_nonneg s := by split_ifs <;> norm_num
  pays s := by
    rw [Real.exp_zero, one_mul, one_mul]
    by_cases h : halted s = true
    · show (if halted (estep s) then (0 : ℝ) else 1) ≤ if halted s then (0 : ℝ) else 1
      simp [halted_mono h, h]
    · show (if halted (estep s) then (0 : ℝ) else 1) ≤ if halted s then (0 : ℝ) else 1
      simp only [h, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> norm_num

theorem estep_iterate (k : ℕ) (c : Code) (n : ℕ) : estep^[k] (start c n) = ((k, c), n) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem etm_balanced_iff (c : Code) (n k : ℕ) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) :
    etm.Balanced ε (start c n) k ↔ ∃ x, x ∈ evaln k c n := by
  unfold RunSys.Balanced
  show (if halted (estep^[k] (start c n)) then (0 : ℝ) else 1) ≤ ε ↔ _
  rw [estep_iterate]
  show (if (evaln k c n).isSome then (0 : ℝ) else 1) ≤ ε ↔ _
  by_cases h : (evaln k c n).isSome = true
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
    simp only [h, ↓reduceIte]
    exact ⟨fun _ => ⟨x, hx⟩, fun _ => h0⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun h' => absurd h' (not_le.2 h1), fun ⟨x, hx⟩ => absurd (Option.isSome_iff_exists.2 ⟨x, hx⟩) h⟩

/-- **The ETM runs its content**: it reaches balance from `start c n` exactly when `c` halts on `n`. -/
theorem etm_runs (c : Code) (n : ℕ) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) :
    etm.Reaches ε (start c n) ↔ (eval c n).Dom := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := (etm_balanced_iff c n k h0 h1).1 hk
    exact ⟨x, evaln_sound hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := evaln_complete.1 hx
    exact ⟨k, (etm_balanced_iff c n k h0 h1).2 ⟨x, hk⟩⟩

/-- **What the ETM reads off at balance is the content's value.** -/
theorem etm_output {c : Code} {n k x : ℕ} (h : evaln k c n = some x) : x ∈ eval c n := evaln_sound h

theorem etm_output_complete {c : Code} {n x : ℕ} (h : x ∈ eval c n) : ∃ k, evaln k c n = some x :=
  evaln_complete.1 h

/-- **Universality in Turing's sense**: every partial recursive function is run by the ETM from some description. -/
theorem etm_universal (f : ℕ →. ℕ) (hf : Nat.Partrec f) : ∃ c : Code, ∀ n, ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
    (etm.Reaches ε (start c n) ↔ (f n).Dom) ∧ ∀ k x, evaln k c n = some x → x ∈ f n := by
  obtain ⟨c, rfl⟩ := Code.exists_code.1 hf
  exact ⟨c, fun n ε h0 h1 => ⟨etm_runs c n h0 h1, fun _ _ h => evaln_sound h⟩⟩

/-- **The ETM's step is primitive recursive.** -/
theorem estep_primrec : Primrec estep :=
  (Primrec.pair (Primrec.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))
    Primrec.snd).of_eq fun _ => rfl

/-- **The ETM's balance test is primitive recursive.** -/
theorem halted_primrec : Primrec halted := Primrec.option_isSome.comp primrec_evaln

/-! ## (c) Turing's limit -/

/-- **No computable predicate decides whether the ETM reaches balance**, for all descriptions (Mathlib's
`ComputablePred.halting_problem`). -/
theorem etm_balance_undecidable (n : ℕ) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) :
    ¬ ComputablePred fun c : Code => etm.Reaches ε (start c n) := fun h =>
  ComputablePred.halting_problem n (ComputablePred.of_eq h fun c => etm_runs c n h0 h1)

/-- **(c1) Binary global truth at G0**: for every content, "the ETM reaches balance" has a truth value, given as a
total `Bool` by classical decidability (`Classical.dec`). The definition is `noncomputable`: the truth exists but cannot
be run. -/
noncomputable def etmTruth (n : ℕ) (c : Code) : Bool :=
  @decide (etm.Reaches (1 / 2) (start c n)) (Classical.dec _)

/-- The truth value is the truth: `true` exactly when the ETM reaches balance. -/
theorem etmTruth_spec (n : ℕ) (c : Code) : etmTruth n c = true ↔ etm.Reaches (1 / 2) (start c n) :=
  @decide_eq_true_iff _ (Classical.dec _)

/-- **Binary**: for every content, the ETM reaches balance or it does not. -/
theorem etm_binary (n : ℕ) (c : Code) : etm.Reaches (1 / 2) (start c n) ∨ ¬ etm.Reaches (1 / 2) (start c n) :=
  Classical.em _

/-- **(c2) No machine computes the global truth**: the truth function of (c1) is not computable. -/
theorem etmTruth_not_computable (n : ℕ) : ¬ Computable (etmTruth n) := fun h =>
  etm_balance_undecidable n (ε := 1 / 2) (by norm_num) (by norm_num) ⟨fun _ => Classical.dec _, h⟩

/-- **(c) in two parts.** (c1) A total, binary truth exists for every content (classically). (c2) It is not
computable. -/
theorem etm_truth_edge (n : ℕ) :
    (∀ c : Code, (etmTruth n c = true ↔ etm.Reaches (1 / 2) (start c n))) ∧ ¬ Computable (etmTruth n) :=
  ⟨etmTruth_spec n, etmTruth_not_computable n⟩

/-- **The ETM is lossless** (factor `1`, cost `0` = floor), hence outside the contraction class. -/
theorem etm_not_contracting (θ : ℝ) : ¬ etm.Contracting θ := fun ⟨h, hq⟩ => by
  have := h (start Code.zero 0)
  simp only [etm, Real.exp_zero, one_mul] at this hq
  linarith

/-- **The exact edge of the ETM claim.** (b) Every running system in the contraction class reaches balance within `ε`
by the explicit computable bound. (c) The ETM, which runs every partial recursive content and is lossless (outside the
class), has an undecidable balance problem. -/
theorem etm_edge :
    (∀ (δ : ℝ) (S : RunSys.{u} δ) (θ : ℝ), S.Contracting θ → ∀ (x : S.X) (M ε q : ℚ),
      Real.exp δ * θ ≤ q → q < 1 → S.mass x ≤ M → 0 < ε → ∀ n ≥ balanceBound M ε q, S.Balanced ε x n) ∧
    (∀ f : ℕ →. ℕ, Nat.Partrec f → ∃ c : Code, ∀ n, (etm.Reaches (1 / 2) (start c n) ↔ (f n).Dom)) ∧
    (∀ θ, ¬ etm.Contracting θ) ∧
    (∀ n, ¬ ComputablePred fun c : Code => etm.Reaches (1 / 2) (start c n)) :=
  ⟨fun _ S _ hS x _ _ _ hq hq1 hM hε => S.reaches_of_contracting hS x hq hq1 hM hε,
    fun f hf => (etm_universal f hf).imp fun _ h n => (h n (1 / 2) (by norm_num) (by norm_num)).1,
    etm_not_contracting,
    fun n => etm_balance_undecidable n (by norm_num) (by norm_num)⟩

end ProofPhase.ETM
