/-
The form layer as one API: a template instance, worked end to end on a toy (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/API.md` (the how-to this file is the example of).
-/

import ProofPhase.API

/-!
# Template: a two-state Markov chain, from nothing to every form-layer theorem

Copy this file to start a new problem. The toy: a coin that flips with probability `p` at each tick. Two observers start
from different beliefs `a` and `b` about "heads"; one tick sends a belief `a` to `flip p a = (1 − p) a + p (1 − a)`. The
question the form layer answers for every such system alike: *do the two beliefs come together, how fast, and how long
until they are `ε` apart?*

The seven steps (the numbers are those of `docs/unified/API.md`):

1. **Input** (`flip`, the numbers `p`, `0 ≤ p ≤ 1`).
2. **Running system** (`chain`): states, step, factor, mass, and the one check of the ledger law.
3. **Open step** (`Mixing`): the one running-state hypothesis, `0 < p < 1`, in the `OpenStep` slot; a proved instance
   (`mixing_quarter`) shows the slot filled.
4. **Ledger, for free** (`toy_carry`, `toy_decay`): the ledger theorems on the system.
5. **Settle bound, for free** (`toy_settles`, `toy_settle_101`): an explicit step count. **5b. The decisions run** (`ticksNeeded`, `#eval`, `ticksNeeded_correct`): computed on rationals, proved right for the real system.
6. **Transport, for free** (`noisy`, `toy_bounded`, `toy_sign`): rounding errors in the computed beliefs, carried along
   the chain, stay bounded and keep the sign.
7. **The card** (`problem`): input + proved structure + the one named open step.

Standard axioms only.
-/

noncomputable section

namespace ProofPhase.API.Template

open ProofPhase.API

/-! ### Step 1. The input -/

/-- One tick of the two-state chain: the belief `a` in "heads" after the coin flips with probability `p`. -/
def flip (p a : ℝ) : ℝ := (1 - p) * a + p * (1 - a)

theorem flip_sub (p a b : ℝ) : flip p a - flip p b = (1 - 2 * p) * (a - b) := by unfold flip; ring

/-! ### Step 2. The running system (the proved structure) -/

/-- **The two-state chain as a running system.** States: a pair of beliefs. Step: both flip. Factor: `|1 − 2p|`, the
Dobrushin coefficient, in `[0, 1]` because `0 ≤ p ≤ 1`. Mass: the distance of the two beliefs. The ledger law (floor
`0`): the distance after a tick is the factor times the distance before. -/
def chain (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : RunSys 0 where
  X := ℝ × ℝ
  step x := (flip p x.1, flip p x.2)
  fac _ := |1 - 2 * p|
  mass x := |x.1 - x.2|
  fac_nonneg _ := abs_nonneg _
  fac_le_one _ := abs_le.2 ⟨by linarith, by linarith⟩
  mass_nonneg _ := abs_nonneg _
  pays x := by
    show |flip p x.1 - flip p x.2| ≤ Real.exp 0 * |1 - 2 * p| * |x.1 - x.2|
    rw [flip_sub, abs_mul, Real.exp_zero, one_mul]

/-! ### Step 3. The open step, in its slot -/

/-- **The open step** of the toy: the coin is not degenerate (`0 < p < 1`), i.e. the factor is strictly below one, a cost
above the floor. Here it is easy; in a real problem it is the statement nobody has proved. -/
def Mixing (p : ℝ) : Prop := OpenStep "the coin is neither fixed nor always flipping" (0 < p ∧ p < 1)

/-- The open step puts the chain in the contraction class. -/
theorem chain_contracting {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : Mixing p) : (chain p hp0 hp1).Contracting |1 - 2 * p| :=
  ⟨fun _ => le_rfl, by rw [Real.exp_zero, one_mul]; exact abs_lt.2 ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩⟩

/-- The slot filled with a proof, for `p = 1/4`. -/
theorem mixing_quarter : Mixing (1 / 4) := by norm_num [Mixing]

/-! ### Step 4. The ledger theorems, for free -/

/-- **Carry**, from the API: the distance after `n` ticks is at most the product of the factors times the start. -/
theorem toy_carry (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ × ℝ) (n : ℕ) :
    |((chain p hp0 hp1).step^[n] x).1 - ((chain p hp0 hp1).step^[n] x).2| ≤
      (∏ _i ∈ Finset.range n, Real.exp 0 * |1 - 2 * p|) * |x.1 - x.2| :=
  (chain p hp0 hp1).carry x n

/-- **Decay**, from the API (`contract`): the distance after `n` ticks is at most `|1 − 2p|^n` times the start. -/
theorem toy_decay (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ × ℝ) (n : ℕ) :
    |((chain p hp0 hp1).step^[n] x).1 - ((chain p hp0 hp1).step^[n] x).2| ≤ |1 - 2 * p| ^ n * |x.1 - x.2| := by
  have := (chain p hp0 hp1).contract (θ := |1 - 2 * p|) (fun _ => le_rfl) x n
  rwa [Real.exp_zero, one_mul] at this

/-! ### Step 5. The settle bound, for free -/

/-- **Settling**, from the API (`settle_everywhere`): under the open step, the two beliefs come within any `ε > 0`. -/
theorem toy_settles {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : Mixing p) (x : ℝ × ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, |((chain p hp0 hp1).step^[n] x).1 - ((chain p hp0 hp1).step^[n] x).2| ≤ ε :=
  settle_everywhere (chain p hp0 hp1) (chain_contracting hp0 hp1 h) x hε

/-- **An explicit count**, from the API (`settle`): for `p = 1/4`, beliefs at distance at most `1` are within `1/100`
after every tick from number `101` on (`balanceBound 1 (1/100) (1/2) = 101`, by the kernel). -/
theorem toy_settle_101 (x : ℝ × ℝ) (hx : |x.1 - x.2| ≤ 1) (n : ℕ) (hn : 101 ≤ n) :
    |((chain (1 / 4) (by norm_num) (by norm_num)).step^[n] x).1 -
      ((chain (1 / 4) (by norm_num) (by norm_num)).step^[n] x).2| ≤ 1 / 100 := by
  have hb : balanceBound (1 : ℚ) (1 / 100) (1 / 2) = 101 := by norm_num [ProofPhase.ETM.balanceBound]
  have h := settle (chain (1 / 4) (by norm_num) (by norm_num)) (θ := |1 - 2 * (1 / 4)|)
    (chain_contracting (by norm_num) (by norm_num) mixing_quarter) x (M := 1) (ε := 1 / 100) (q := 1 / 2)
    (by rw [Real.exp_zero, one_mul]; norm_num [abs_of_pos]) (by norm_num) (by show |x.1 - x.2| ≤ _; push_cast; exact hx) (by norm_num) n
    (by rw [hb]; exact hn)
  exact h.trans_eq (by push_cast; norm_num)

/-! ### Step 5b. The decisions run (the computable side)

Everything above is a statement about real numbers: truth, not computation. The decisions the system makes (how many ticks
until the beliefs are within `ε`; the factor; the ledger check) are computed on rationals, and a theorem says the computed
answer is right for the real system. The `#eval`s below run when the file is checked. -/

section Computable

/-- One tick on rational beliefs. -/
def flipQ (p a : ℚ) : ℚ := (1 - p) * a + p * (1 - a)

/-- The factor, computed. -/
def factorQ (p : ℚ) : ℚ := |1 - 2 * p|

/-- The distance of two beliefs after `n` ticks, computed. -/
def distQ (p a b : ℚ) (n : ℕ) : ℚ := |(flipQ p)^[n] a - (flipQ p)^[n] b|

/-- **The decision**: the number of ticks after which beliefs at distance at most `1` are within `ε`: the API's
`balanceBound` at the computed factor. -/
def ticksNeeded (p ε : ℚ) : ℕ := balanceBound 1 ε (factorQ p)

#eval ticksNeeded (1 / 4) (1 / 100)
#eval distQ (1 / 4) 1 0 (ticksNeeded (1 / 4) (1 / 100))
#guard ticksNeeded (1 / 4) (1 / 100) = 101
#guard decide (distQ (1 / 4) 1 0 (ticksNeeded (1 / 4) (1 / 100)) ≤ 1 / 100)
#guard decide (PaysQ (fun i => (1 / 2 : ℚ) ^ i) (fun _ => 1 / 2) 10)

end Computable

theorem flipQ_cast (p a : ℚ) : ((flipQ p a : ℚ) : ℝ) = flip (p : ℝ) (a : ℝ) := by
  simp [flipQ, flip]

theorem flipQ_iter_cast (p a : ℚ) (n : ℕ) : (((flipQ p)^[n] a : ℚ) : ℝ) = (flip (p : ℝ))^[n] (a : ℝ) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, flipQ_cast]

theorem chain_iter (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ × ℝ) (n : ℕ) :
    (chain p hp0 hp1).step^[n] x = ((flip p)^[n] x.1, (flip p)^[n] x.2) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih ((chain p hp0 hp1).step x)

/-- **The computed answer is right for the real system.** If the computed factor is below one, the tolerance is positive
and the beliefs start within `1`, then from tick `ticksNeeded p ε` on the computed distance is at most `ε`. The decision
runs on `ℚ`; the justification is `settle0` of the API on the real chain. -/
theorem ticksNeeded_correct {p ε : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : factorQ p < 1) (hε : 0 < ε) {a b : ℚ}
    (hab : |a - b| ≤ 1) (n : ℕ) (hn : ticksNeeded p ε ≤ n) : distQ p a b n ≤ ε := by
  have hp0' : (0 : ℝ) ≤ p := by exact_mod_cast hp0
  have hp1' : (p : ℝ) ≤ 1 := by exact_mod_cast hp1
  have key := settle0 (chain (p : ℝ) hp0' hp1') (q := factorQ p) hq
    (fun _ => le_of_eq (by simp [chain, factorQ])) ((a : ℝ), (b : ℝ)) (M := 1) (ε := ε)
    (by show |(a : ℝ) - (b : ℝ)| ≤ ((1 : ℚ) : ℝ); exact_mod_cast hab) hε n hn
  have h2 : ((distQ p a b n : ℚ) : ℝ) ≤ ((ε : ℚ) : ℝ) := by
    have e : ((distQ p a b n : ℚ) : ℝ) =
        |((flip (p : ℝ))^[n] (a : ℝ)) - (flip (p : ℝ))^[n] (b : ℝ)| := by
      unfold distQ
      rw [Rat.cast_abs, Rat.cast_sub, flipQ_iter_cast, flipQ_iter_cast]
    rw [e]
    unfold ProofPhase.ETM.RunSys.Balanced at key
    rw [chain_iter] at key
    exact key
  exact_mod_cast h2

/-! ### Step 6. Transport, for free -/

/-- A computed trajectory `y`: each tick adds a rounding error `w n` of size at most `R` to the exact tick. -/
structure Noisy (p R : ℝ) where
  y : ℕ → ℝ
  w : ℕ → ℝ
  hw : ∀ n, |w n| ≤ R
  hy : ∀ n, y (n + 1) = flip p (y n) + w n

/-- **The error of the computed trajectory against the exact one is an `Uncertainty`**: error bound `|y n − x n|`, factor
`|1 − 2p|`, fresh uncertainty `R` per tick. -/
def noisy {p R : ℝ} (hR : 0 ≤ R) (N : Noisy p R) (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = flip p (x n)) : Uncertainty 0 where
  e n := |N.y n - x n|
  f _ := |1 - 2 * p|
  r _ := R
  e0_nonneg := abs_nonneg _
  f_nonneg _ := abs_nonneg _
  r_nonneg _ := hR
  step n := by
    show |N.y (n + 1) - x (n + 1)| ≤ Real.exp 0 * |1 - 2 * p| * |N.y n - x n| + R
    rw [N.hy, hx, Real.exp_zero, one_mul]
    have h : flip p (N.y n) + N.w n - flip p (x n) = (1 - 2 * p) * (N.y n - x n) + N.w n := by
      rw [← flip_sub]; ring
    rw [h, ← abs_mul]
    exact (abs_add_le _ _).trans (by linarith [N.hw n])

/-- **Bounded transport**, from the API: for `p = 1/4`, an exact start and rounding errors at most `R`, the computed
trajectory stays within `2R` of the exact one at every tick. -/
theorem toy_bounded {R : ℝ} (hR : 0 ≤ R) (N : Noisy (1 / 4) R) (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = flip (1 / 4) (x n))
    (h0 : N.y 0 = x 0) (n : ℕ) : |N.y n - x n| ≤ 2 * R := by
  have h : |N.y n - x n| ≤ (noisy hR N x hx).e 0 + R / (1 - Real.exp 0 * (1 / 2)) :=
    (noisy hR N x hx).bounded (θ := 1 / 2) (R := R) (fun _ => by show |1 - 2 * (1 / 4)| ≤ (1 / 2 : ℝ); norm_num [abs_of_pos])
      (by rw [Real.exp_zero]; norm_num) (fun _ => le_rfl) n
  have e0 : (noisy hR N x hx).e 0 = 0 := by show |N.y 0 - x 0| = 0; rw [h0, sub_self, abs_zero]
  rw [e0, Real.exp_zero] at h
  linarith [show R / (1 - 1 * (1 / 2)) = 2 * R by ring]

/-- The exact beliefs from the start `1` at `p = 1/4`: `1/2 + (1/2)^(n+1)`, never below `1/2`. -/
def exact (n : ℕ) : ℝ := 1 / 2 + (1 / 2) ^ (n + 1)

theorem exact_succ (n : ℕ) : exact (n + 1) = flip (1 / 4) (exact n) := by unfold exact flip; ring

/-- **Sign preserved**, from the API: the exact belief never drops below the margin `1/2`; computed beliefs with rounding
errors below `1/8` (any below `1/4` would do) stay positive at every tick. -/
theorem toy_sign {R : ℝ} (hR0 : 0 ≤ R) (hR : R < 1 / 8) (N : Noisy (1 / 4) R) (h0 : N.y 0 = 1) (n : ℕ) : 0 < N.y n := by
  refine (noisy hR0 N exact exact_succ).sign_of_bounded (m := fun _ => 1 / 2) (μ := 1 / 2) (M := exact) (N := N.y)
    (θ := 1 / 2) (R := R)
    (fun n => by show (1 / 2 : ℝ) ≤ exact n; unfold exact; linarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) (n + 1)])
    (fun _ => le_rfl) (fun n => le_rfl)
    (fun _ => by show |1 - 2 * (1 / 4)| ≤ (1 / 2 : ℝ); norm_num [abs_of_pos]) (by rw [Real.exp_zero]; norm_num)
    (fun _ => le_rfl) ?_ n
  have e0 : (noisy hR0 N exact exact_succ).e 0 = 0 := by
    show |N.y 0 - exact 0| = 0
    rw [h0]; unfold exact; norm_num
  rw [e0, Real.exp_zero]
  linarith [show R / (1 - 1 * (1 / 2)) = 2 * R by ring]

/-! ### Step 7. The card -/

/-- **The toy as a problem card.** Input: a coin bias `p ∈ [0, 1]`. Open step: `Mixing p`. Conclusion: two observers'
beliefs come within any `ε`, from any start. Proved structure: step 5. -/
def problem : Problem where
  name := "Two-state chain: beliefs come together"
  Input := {p : ℝ // 0 ≤ p ∧ p ≤ 1}
  Open i := Mixing i.1
  Concl i := ∀ (x : ℝ × ℝ) (ε : ℝ), 0 < ε → ∃ n,
    |((chain i.1 i.2.1 i.2.2).step^[n] x).1 - ((chain i.1 i.2.1 i.2.2).step^[n] x).2| ≤ ε
  proved i h x _ hε := toy_settles i.2.1 i.2.2 h x hε

end ProofPhase.API.Template
