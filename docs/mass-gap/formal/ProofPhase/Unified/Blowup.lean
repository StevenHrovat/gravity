/-
The unified lossy-step theorem: the rescaled-frame ledger of a stable self-similar blowup (2026-11-23).
Released under Apache 2.0.

Note: `docs/unified/BLOWUP.md`. Blueprint: Chen and Hou, stable nearly self-similar blowup of 2D Boussinesq and 3D
axisymmetric Euler with smooth data and a boundary (arXiv 2210.07191, 2305.05660). Nothing about Euler is proved here.
-/

import ProofPhase.Unified.Ledger

/-!
# A one-scale certificate in rescaled time forces arrival at a finite boundary time

A discrete skeleton of the bootstrap in a dynamically rescaled (self-similar) frame. Steps are unit intervals of rescaled
time. Two quantities are carried:

* `M i ≥ 0`, the size of the perturbation away from the profile (in the paper: a weighted norm). One step obeys
  `M (i+1) ≤ q M i + C (M i)^2 + r`: linear damping `q = e^{-λ}`, nonlinear constant `C`, residual `r` of the approximate
  profile. Scale invariance makes `q, C, r` the same at every step.
* `d i > 0`, the physical duration of step `i` (in the paper: the amplitude normalisation `C_ω(τ)`). One step multiplies
  it by `e^{a i}`, and `a i ≤ c̄ + K M i`, `c̄` the profile's focusing rate.

**Results.**
* `trap`: an invariant ball. If `q R + C R^2 + r ≤ R` and `M 0 ≤ R`, then `M n ≤ R` for every `n`.
* `trap_radius`, `trap_of_gap`: the ball exists (radius `(1 - q)/(2C)`) when `(1 - q)^2 ≥ 4 C r`.
* `gap_of_costAboveFloor`: that condition in the ledger's language, `CostAboveFloor` of the damping `1 - q` over the floor
  `2 √(C r)`, with one step type only (`Ω = Unit`).
* `escape_of_below`, `escape_pos`: the condition is sharp for the comparison recursion: with equality in the step and
  `(1 - q)^2 < 4 C r`, `M` grows at least linearly, so no ball traps it.
* `durations_pay`, `arrival`: focusing `a i ≤ -γ < 0` makes the durations a decay ledger (floor 0, cost `γ`): they are
  summable, so infinitely many rescaled steps fit in a finite physical time `T* = Σ d i ≤ 1/(1 - e^{-γ})`.
* `amplitude_unbounded`: the amplitude `1/d n ≥ e^{γ n}` tends to infinity.
* `blowup_of_certificate`: the assembly. The one-scale certificate (`(1 - q)^2 ≥ 4 C r`, `c̄ + K R ≤ -γ < 0`, `M 0 ≤ R`)
  gives: the perturbation stays in the ball forever, the total physical time is finite, the amplitude is unbounded.

What is **not** here: the PDE. The step inequality for `M` is, in Chen-Hou, a theorem about weighted norms whose constants
are certified by rigorous numerics; here it is a hypothesis. No axioms beyond the standard ones; no unproved steps.
-/

open Finset Filter Topology

noncomputable section

namespace ProofPhase.Unified

/-! ### 1. The trapping ball -/

/-- **The invariant ball.** A one-step bound `M (i+1) ≤ q M i + C (M i)^2 + r` with nonnegative constants, a radius `R`
with `q R + C R^2 + r ≤ R`, and a start inside the ball: the perturbation stays in the ball at every step. -/
theorem trap {M : ℕ → ℝ} {q C r R : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C) (hM : ∀ i, 0 ≤ M i)
    (hstep : ∀ i, M (i + 1) ≤ q * M i + C * M i ^ 2 + r) (hR : q * R + C * R ^ 2 + r ≤ R) (h0 : M 0 ≤ R) :
    ∀ n, M n ≤ R := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have h1 : q * M n ≤ q * R := mul_le_mul_of_nonneg_left ih hq
    have h2 : M n ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (hM n) ih 2
    have h3 : C * M n ^ 2 ≤ C * R ^ 2 := mul_le_mul_of_nonneg_left h2 hC
    linarith [hstep n]

/-- **The radius.** If `(1 - q)^2 ≥ 4 C r` with `C > 0`, the radius `R = (1 - q)/(2C)` satisfies `q R + C R^2 + r ≤ R`. -/
theorem trap_radius {q C r : ℝ} (hC : 0 < C) (hgap : 4 * C * r ≤ (1 - q) ^ 2) :
    q * ((1 - q) / (2 * C)) + C * ((1 - q) / (2 * C)) ^ 2 + r ≤ (1 - q) / (2 * C) := by
  have hC' : C ≠ 0 := hC.ne'
  have key : q * ((1 - q) / (2 * C)) + C * ((1 - q) / (2 * C)) ^ 2 + r - (1 - q) / (2 * C) =
      (4 * C * r - (1 - q) ^ 2) / (4 * C) := by
    field_simp
    ring
  have : (4 * C * r - (1 - q) ^ 2) / (4 * C) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  linarith

/-- **The one-scale certificate traps the perturbation.** Damping `q < 1`, nonlinear constant `C > 0`, residual `r ≥ 0`
with `(1 - q)^2 ≥ 4 C r`, and a start within `(1 - q)/(2C)`: the perturbation stays within that radius forever. -/
theorem trap_of_gap {M : ℕ → ℝ} {q C r : ℝ} (hq : 0 ≤ q) (hC : 0 < C) (hM : ∀ i, 0 ≤ M i)
    (hstep : ∀ i, M (i + 1) ≤ q * M i + C * M i ^ 2 + r) (hgap : 4 * C * r ≤ (1 - q) ^ 2)
    (h0 : M 0 ≤ (1 - q) / (2 * C)) : ∀ n, M n ≤ (1 - q) / (2 * C) :=
  trap hq hC.le hM hstep (trap_radius hC hgap) h0

/-- **The certificate in the ledger's language.** Cost above floor for the single step type of the rescaled frame
(`Ω = Unit`: scale invariance leaves one step to check), with the damping `1 - q` as the cost and `2 √(C r)` as the floor,
gives the trapping condition. -/
theorem gap_of_costAboveFloor {q C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (h : CostAboveFloor (fun _ : Unit => 1 - q) (2 * √(C * r))) : 4 * C * r ≤ (1 - q) ^ 2 := by
  obtain ⟨κ, hκ, hle⟩ := h
  have hle' : κ ≤ 1 - q := hle ()
  have hs : 0 ≤ 2 * √(C * r) := by positivity
  have hsq : (2 * √(C * r)) ^ 2 = 4 * C * r := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hC hr)]; ring
  have : (2 * √(C * r)) ^ 2 ≤ (1 - q) ^ 2 := pow_le_pow_left₀ hs (hκ.le.trans hle') 2
  linarith

/-- **The floor is a true floor.** For the comparison recursion with equality, every step adds at least
`r - (1 - q)^2/(4C)`, which is positive when `(1 - q)^2 < 4 C r` (`escape_pos`): the perturbation then grows at least
linearly and no ball traps it. -/
theorem escape_of_below {M : ℕ → ℝ} {q C r : ℝ} (hC : 0 < C)
    (hstep : ∀ i, M (i + 1) = q * M i + C * M i ^ 2 + r) (n : ℕ) :
    M 0 + n * (r - (1 - q) ^ 2 / (4 * C)) ≤ M n := by
  have hinc : ∀ i, M i + (r - (1 - q) ^ 2 / (4 * C)) ≤ M (i + 1) := by
    intro i
    have hsq : 0 ≤ C * (M i - (1 - q) / (2 * C)) ^ 2 := mul_nonneg hC.le (sq_nonneg _)
    have hexp : C * (M i - (1 - q) / (2 * C)) ^ 2 =
        C * M i ^ 2 - (1 - q) * M i + (1 - q) ^ 2 / (4 * C) := by
      field_simp
      ring
    rw [hstep i]
    nlinarith [hsq, hexp]
  induction n with
  | zero => simp
  | succ n ih =>
    have := hinc n
    push_cast
    linarith

/-- Below the floor the per-step increment of `escape_of_below` is positive. -/
theorem escape_pos {q C r : ℝ} (hC : 0 < C) (hbelow : (1 - q) ^ 2 < 4 * C * r) :
    0 < r - (1 - q) ^ 2 / (4 * C) := by
  have : (1 - q) ^ 2 / (4 * C) < r := by rw [div_lt_iff₀ (by linarith)]; linarith
  linarith

/-! ### 2. Rescaled steps in finite physical time -/

/-- The physical durations of the rescaled steps: `d 0 = 1`, `d (i+1) = e^{a i} d i`. -/
def durations (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => Real.exp (a n) * durations a n

theorem durations_pos (a : ℕ → ℝ) (n : ℕ) : 0 < durations a n := by
  induction n with
  | zero => simp [durations]
  | succ n ih => exact mul_pos (Real.exp_pos _) ih

/-- **Focusing is a decay ledger.** With `a i ≤ -γ`, the durations pay the cost `γ` at every step, floor 0. -/
theorem durations_pay {a : ℕ → ℝ} {γ : ℝ} (ha : ∀ i, a i ≤ -γ) (n : ℕ) :
    Pays (durations a) (fun _ => γ) 0 n := fun i _ => by
  show Real.exp (a i) * durations a i ≤ Real.exp (0 - γ) * durations a i
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith [ha i])) (durations_pos a i).le

/-- **Arrival at a finite time.** With a focusing rate `γ > 0`, the durations decay like `e^{-γ n}` and are summable:
infinitely many rescaled steps fit in the finite physical time `T* = Σ d i`, and `T* ≤ 1/(1 - e^{-γ})`. -/
theorem arrival {a : ℕ → ℝ} {γ : ℝ} (hγ : 0 < γ) (ha : ∀ i, a i ≤ -γ) :
    (∀ n, durations a n ≤ Real.exp (-(n * γ))) ∧ Summable (durations a) ∧
      ∑' n, durations a n ≤ 1 / (1 - Real.exp (-γ)) := by
  have hd0 : durations a 0 = 1 := rfl
  have hdec : ∀ n, durations a n ≤ Real.exp (-(n * γ)) := fun n => by
    have := decay (durations_pay ha n) (fun _ _ => le_refl γ) (by rw [hd0]; norm_num)
    simpa [hd0, sub_zero] using this
  have hsum := summable_of_gap (fun n => durations_pay ha n) (fun _ => le_refl γ) hγ
    (fun n => (durations_pos a n).le)
  refine ⟨hdec, hsum, ?_⟩
  have hq0 : 0 ≤ Real.exp (-γ) := (Real.exp_pos _).le
  have hq1 : Real.exp (-γ) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hgeo : ∀ n, durations a n ≤ Real.exp (-γ) ^ n := fun n => by
    rw [← Real.exp_nat_mul, show (n : ℝ) * -γ = -(n * γ) by ring]; exact hdec n
  calc ∑' n, durations a n ≤ ∑' n : ℕ, Real.exp (-γ) ^ n :=
        hsum.tsum_le_tsum hgeo (summable_geometric_of_lt_one hq0 hq1)
    _ = 1 / (1 - Real.exp (-γ)) := by rw [tsum_geometric_of_lt_one hq0 hq1, one_div]

/-- **The amplitude is unbounded.** With `a i ≤ -γ < 0`, the amplitude `1/d n` is at least `e^{γ n}` and tends to
infinity. -/
theorem amplitude_unbounded {a : ℕ → ℝ} {γ : ℝ} (hγ : 0 < γ) (ha : ∀ i, a i ≤ -γ) :
    (∀ n : ℕ, Real.exp (n * γ) ≤ (durations a n)⁻¹) ∧ Tendsto (fun n => (durations a n)⁻¹) atTop atTop := by
  have hlow : ∀ n : ℕ, Real.exp (n * γ) ≤ (durations a n)⁻¹ := fun n => by
    have h := (arrival hγ ha).1 n
    rw [Real.exp_neg] at h
    exact (le_inv_comm₀ (durations_pos a n) (Real.exp_pos _)).1 h
  refine ⟨hlow, tendsto_atTop_mono hlow ?_⟩
  refine Real.tendsto_exp_atTop.comp ?_
  exact tendsto_natCast_atTop_atTop.atTop_mul_const hγ

/-! ### 3. The assembly -/

/-- **A one-scale certificate forces blowup at a finite time.** In the rescaled frame:
* the perturbation obeys `M (i+1) ≤ q M i + C (M i)^2 + r` with the same constants at every step (scale invariance);
* the certificate: `(1 - q)^2 ≥ 4 C r` and a start within `R = (1 - q)/(2C)`;
* the duration exponent obeys `a i ≤ c̄ + K M i`, and the profile focuses with margin: `c̄ + K R ≤ -γ < 0`.

Then the perturbation stays within `R` forever, the physical durations sum to a finite `T*`, and the amplitude tends to
infinity: the existence interval in physical time ends at `T*`. -/
theorem blowup_of_certificate {M a : ℕ → ℝ} {q C r K cbar γ : ℝ} (hq : 0 ≤ q) (hC : 0 < C) (hK : 0 ≤ K)
    (hM : ∀ i, 0 ≤ M i) (hstep : ∀ i, M (i + 1) ≤ q * M i + C * M i ^ 2 + r)
    (hgap : 4 * C * r ≤ (1 - q) ^ 2) (h0 : M 0 ≤ (1 - q) / (2 * C))
    (ha : ∀ i, a i ≤ cbar + K * M i) (hfocus : cbar + K * ((1 - q) / (2 * C)) ≤ -γ) (hγ : 0 < γ) :
    (∀ n, M n ≤ (1 - q) / (2 * C)) ∧ Summable (durations a) ∧
      ∑' n, durations a n ≤ 1 / (1 - Real.exp (-γ)) ∧ Tendsto (fun n => (durations a n)⁻¹) atTop atTop := by
  have htrap := trap_of_gap hq hC hM hstep hgap h0
  have ha' : ∀ i, a i ≤ -γ := fun i => by
    have := mul_le_mul_of_nonneg_left (htrap i) hK
    linarith [ha i]
  obtain ⟨_, hsum, hT⟩ := arrival hγ ha'
  exact ⟨htrap, hsum, hT, (amplitude_unbounded hγ ha').2⟩

/-- **The boundary quantum (the Beale-Kato-Majda count).** Per rescaled step the amplitude times the duration is
`1`: the physical amplitude `1/d n` integrated over the step's duration `d n` gives one quantum, the rescaled amplitude.
So after `n` steps the count is `n`, unbounded, while the elapsed time stays below `T*`. -/
theorem boundary_quantum (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, (durations a i)⁻¹ * durations a i = n := by
  simp [inv_mul_cancel₀ (durations_pos a _).ne']

end ProofPhase.Unified
