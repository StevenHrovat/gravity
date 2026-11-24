/-
The unified lossy-step theorem: the two open encoder steps through the lens of GRH (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/GRH-LENS.md`.
-/

import ProofPhase.Unified.Encoder

/-!
# Through the lens of GRH: one Schur-Caratheodory structure, and what positivity does and does not give

**1. The two loss profiles are two faces of one structure** (lead 2).
* `re_cayley`: for every complex `c`, the Cayley transform `F = (1 − c)/(1 + c)` has
  `re F = (1 − ‖c‖²) / ‖1 + c‖²`: the Caratheodory face is the Szego face divided by `‖1 + c‖²`.
* `schur_iff_caratheodory`: `‖c‖ ≤ 1` (Schur class) exactly when `re F ≥ 0` (Caratheodory class).
* `cayley_ofReal`, `elec_eq_szego`: on the real line the Cayley transform is the electric profile, and
  `elec c = szego c / (1 + c)²`.

**2. The centre twist is the one-step (`ℤ/2`) case** (lead 2).
* `z2_sectors`: two nonnegative sector weights `p₀ > 0, p₁ ≥ 0` (electric flux `e = 0, 1`) give the reflection
  coefficient `c = (p₀ − p₁)/(p₀ + p₁)` in `[−1, 1]`, the electric factor `p₁/p₀` and the Szego factor
  `4 p₀ p₁/(p₀ + p₁)²`.
* `z2_realize`: every `c` in `[−1, 1]` comes from such a pair: positivity puts no constraint on `c` beyond the disk.
* `oneBox_sector`: the one-box bound `elec c ≤ 1/μ` is the sector domination `μ p₁ ≤ p₀`, not a positivity statement.

**3. Positivity along a transfer chain** (lead 1, the time direction). For a positive spectral sum
`t k = Σ_a w_a x_a^k` (`w ≥ 0`, `x ≥ 0`, reflection positivity):
* `mom_logconvex`: `t(k+1)² ≤ t(k) t(k+2)` (Cauchy-Schwarz);
* `stepRatio_mono`: the per-step factor `t(k+1)/t(k)` rises with `k`, so the per-step cost (the effective mass) falls:
  a short-distance check overestimates the rate;
* `step_le_of_support`: a gap (`x ≤ ρ`) bounds every step factor by `ρ`;
* `localizing_nonneg`: a gap makes every finite section of the localizing form `ρ t(i+j) − t(i+j+1)` positive. The
  converse is the classical Hausdorff moment theorem (not formalized). So "gap at rate `−log ρ`" has the same shape as
  GRH's sign: positivity of every finite section of one structured form.

**4. The half-turn** (the owner's rotation). `halfTurn = (1/√2) [[−1, 1], [1, 1]]` is symmetric and an involution
(`halfTurn_transpose`, `halfTurn_mul_self`), so orthogonal: a rotation of the Riemann sphere by 180 degrees, up to phase.
Its Moebius action is the electric profile (`halfTurn_mobius`). Its fixed points `√2 − 1` (`elec_selfdual`) and
`−(1 + √2)` (`elec_fixed_neg`) are antipodal (`fixed_antipodal`).

**5. The hyperbolic ledger.** `elec_cost`: the electric cost is the Poincare distance `log((1 + c)/(1 − c))` from the
lossless point `c = 0`; `szego_of_elec`: the Szego factor is `4f/(1 + f)²` of the electric factor `f`, so both profiles
are functions of that one distance. `elec_oplus`: under `a ⊕ b = (a + b)/(1 + ab)` (series) the electric factors multiply
and the costs add; `elec_mul`: the half-turn carries the product of reflection coefficients (parallel) to `⊕` (series).
`two_steps_short`, `three_steps_clear`: two lossless hand-over steps stay below the one-box floor for `μ ≥ 6`, three
clear it for `μ ≤ 14`.

**6. NP.** `separates_swap`: swapping the two sides of a split negates the separator: the same kind of involution, which
exchanges the pictures and leaves the cost unchanged.

**7. The twist form and two boxes.** `oneBox_twist_form`: O1's bound `elec c ≤ 1/μ` is `F_tw ≤ log((μ+1)/(μ−1))`.
`xor_product`: independent boxes side by side multiply their coefficients. `twoBox_defect`: the departure from the
product is the determinant `4 (p₀₀ p₁₁ − p₀₁ p₁₀)/S²` of the joint label law.

No axioms beyond the standard ones.
-/

open Finset

noncomputable section

namespace ProofPhase.Unified

/-! ## 1. The Schur-Caratheodory structure -/

/-- The Cayley transform `F = (1 − c)/(1 + c)`: Schur value `c` to Caratheodory value `F`. -/
def cayley (c : ℂ) : ℂ := (1 - c) / (1 + c)

/-- **The Caratheodory face is the Szego face over `‖1 + c‖²`.** -/
theorem re_cayley (c : ℂ) : (cayley c).re = szego c / Complex.normSq (1 + c) := by
  rw [cayley, Complex.div_re, szego, Complex.sq_norm, ← add_div]
  congr 1
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.sub_im, Complex.one_im, Complex.add_im,
    Complex.normSq_apply]
  ring

/-- **Schur class iff Caratheodory class**: `‖c‖ ≤ 1` exactly when `re F ≥ 0`. -/
theorem schur_iff_caratheodory {c : ℂ} (h : c ≠ -1) : ‖c‖ ≤ 1 ↔ 0 ≤ (cayley c).re := by
  have hN : 0 < Complex.normSq (1 + c) := Complex.normSq_pos.2 fun h0 => h (by linear_combination h0)
  rw [re_cayley, div_nonneg_iff]
  constructor
  · intro hc; exact Or.inl ⟨szego_nonneg hc, hN.le⟩
  · rintro (⟨hs, -⟩ | ⟨-, hN'⟩)
    · unfold szego at hs; nlinarith [norm_nonneg c]
    · exact absurd hN' (not_le.2 hN)

/-- **On the real line the Cayley transform is the electric profile.** -/
theorem cayley_ofReal (c : ℝ) : cayley c = ((elec c : ℝ) : ℂ) := by
  simp only [cayley, elec, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one]

/-- **The electric profile is the Szego profile over `(1 + c)²`.** -/
theorem elec_eq_szego {c : ℝ} (h : c ≠ -1) : elec c = szego c / (1 + c) ^ 2 := by
  have h' : 1 + c ≠ 0 := fun h0 => h (by linarith)
  unfold elec szego
  rw [Real.norm_eq_abs, sq_abs]
  field_simp
  ring

/-! ## 2. The centre twist as the `ℤ/2` case -/

/-- **Two sector weights give one encoder**: `c = (p₀ − p₁)/(p₀ + p₁)` lies in `[−1, 1]`, its electric factor is
`p₁/p₀`, its Szego factor `4 p₀ p₁/(p₀ + p₁)²`. -/
theorem z2_sectors {p₀ p₁ : ℝ} (h0 : 0 < p₀) (h1 : 0 ≤ p₁) :
    ‖(p₀ - p₁) / (p₀ + p₁)‖ ≤ 1 ∧ elec ((p₀ - p₁) / (p₀ + p₁)) = p₁ / p₀ ∧
      szego ((p₀ - p₁) / (p₀ + p₁)) = 4 * p₀ * p₁ / (p₀ + p₁) ^ 2 := by
  have hS : 0 < p₀ + p₁ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hS, div_le_one hS]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · rw [elec, one_sub_div hS.ne', one_add_div hS.ne', div_div_div_cancel_right₀ hS.ne',
      div_eq_div_iff (by linarith) h0.ne']
    ring
  · unfold szego
    rw [Real.norm_eq_abs, sq_abs, div_pow]
    field_simp
    ring

/-- **Freeness**: every `c` in `[−1, 1]` is the encoder of a nonnegative pair of sector weights. -/
theorem z2_realize {c : ℝ} (hc : |c| ≤ 1) :
    0 ≤ (1 + c) / 2 ∧ 0 ≤ (1 - c) / 2 ∧ c = ((1 + c) / 2 - (1 - c) / 2) / ((1 + c) / 2 + (1 - c) / 2) := by
  have := abs_le.1 hc
  refine ⟨by linarith, by linarith, ?_⟩
  field_simp
  ring

/-- **The one-box bound is a sector domination**: `elec c ≤ 1/μ` exactly when `μ p₁ ≤ p₀`. -/
theorem oneBox_sector {p₀ p₁ μ : ℝ} (h0 : 0 < p₀) (h1 : 0 ≤ p₁) (hμ : 0 < μ) :
    elec ((p₀ - p₁) / (p₀ + p₁)) ≤ μ⁻¹ ↔ μ * p₁ ≤ p₀ := by
  rw [(z2_sectors h0 h1).2.1, div_le_iff₀ h0]
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h hμ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul] at this
  · intro h
    have := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hμ.le)
    rwa [← mul_assoc, inv_mul_cancel₀ hμ.ne', one_mul] at this

/-! ## 3. Positivity along a transfer chain -/

section Chain

variable {ι : Type*} (s : Finset ι) (w x : ι → ℝ)

/-- A positive spectral sum `t k = Σ_a w_a x_a^k` (the correlation at distance `k`). -/
def mom (k : ℕ) : ℝ := ∑ a ∈ s, w a * x a ^ k

variable {s w x}

/-- **Log-convexity** (Cauchy-Schwarz): `t(k+1)² ≤ t(k) t(k+2)`. -/
theorem mom_logconvex (hw : ∀ a ∈ s, 0 ≤ w a) (hx : ∀ a ∈ s, 0 ≤ x a) (k : ℕ) :
    mom s w x (k + 1) ^ 2 ≤ mom s w x k * mom s w x (k + 2) := by
  have hnn : ∀ a ∈ s, 0 ≤ w a * x a ^ k := fun a ha => mul_nonneg (hw a ha) (pow_nonneg (hx a ha) k)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun a => √(w a * x a ^ k)) (fun a => √(w a * x a ^ k) * x a)
  have e1 : ∑ a ∈ s, √(w a * x a ^ k) * (√(w a * x a ^ k) * x a) = mom s w x (k + 1) := by
    unfold mom
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← mul_assoc, Real.mul_self_sqrt (hnn a ha)]
    ring
  have e2 : ∑ a ∈ s, √(w a * x a ^ k) ^ 2 = mom s w x k :=
    Finset.sum_congr rfl fun a ha => Real.sq_sqrt (hnn a ha)
  have e3 : ∑ a ∈ s, (√(w a * x a ^ k) * x a) ^ 2 = mom s w x (k + 2) := by
    unfold mom
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [mul_pow, Real.sq_sqrt (hnn a ha)]
    ring
  rw [e1, e2, e3] at hcs
  exact hcs

/-- **The per-step factor rises along the chain**: `t(k+1)/t(k) ≤ t(k+2)/t(k+1)`. Equivalently the per-step cost, the
effective mass `−log(t(k+1)/t(k))`, falls with distance. -/
theorem stepRatio_mono (hw : ∀ a ∈ s, 0 ≤ w a) (hx : ∀ a ∈ s, 0 ≤ x a) (hpos : ∀ k, 0 < mom s w x k) (k : ℕ) :
    mom s w x (k + 1) / mom s w x k ≤ mom s w x (k + 2) / mom s w x (k + 1) := by
  rw [div_le_div_iff₀ (hpos k) (hpos (k + 1))]
  nlinarith [mom_logconvex hw hx k]

/-- **The effective mass falls with distance.** -/
theorem effMass_anti (hw : ∀ a ∈ s, 0 ≤ w a) (hx : ∀ a ∈ s, 0 ≤ x a) (hpos : ∀ k, 0 < mom s w x k) (k : ℕ) :
    -Real.log (mom s w x (k + 2) / mom s w x (k + 1)) ≤ -Real.log (mom s w x (k + 1) / mom s w x k) :=
  neg_le_neg (Real.log_le_log (div_pos (hpos _) (hpos _)) (stepRatio_mono hw hx hpos k))

/-- **A gap bounds every step factor**: if every `x_a ≤ ρ`, then `t(k+1) ≤ ρ t(k)`. -/
theorem step_le_of_support {ρ : ℝ} (hw : ∀ a ∈ s, 0 ≤ w a) (hx : ∀ a ∈ s, 0 ≤ x a) (hxρ : ∀ a ∈ s, x a ≤ ρ)
    (k : ℕ) : mom s w x (k + 1) ≤ ρ * mom s w x k := by
  unfold mom
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [pow_succ]
  have := mul_le_mul_of_nonneg_left (hxρ a ha) (mul_nonneg (hw a ha) (pow_nonneg (hx a ha) k))
  linarith

/-- **A gap gives the sign at every section**: if every `x_a ≤ ρ`, every finite section of the localizing form
`ρ t(i+j) − t(i+j+1)` is positive. -/
theorem localizing_nonneg {ρ : ℝ} (hw : ∀ a ∈ s, 0 ≤ w a) (hxρ : ∀ a ∈ s, x a ≤ ρ) (n : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range n, ∑ j ∈ range n, c i * c j * (ρ * mom s w x (i + j) - mom s w x (i + j + 1)) := by
  have key : ∀ i j, c i * c j * (ρ * mom s w x (i + j) - mom s w x (i + j + 1)) =
      ∑ a ∈ s, w a * (ρ - x a) * ((c i * x a ^ i) * (c j * x a ^ j)) := by
    intro i j
    unfold mom
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pow_succ, pow_add]
    ring
  have hsum : ∑ i ∈ range n, ∑ j ∈ range n, c i * c j * (ρ * mom s w x (i + j) - mom s w x (i + j + 1)) =
      ∑ a ∈ s, w a * (ρ - x a) * (∑ i ∈ range n, c i * x a ^ i) ^ 2 := by
    simp_rw [key]
    calc ∑ i ∈ range n, ∑ j ∈ range n, ∑ a ∈ s, w a * (ρ - x a) * ((c i * x a ^ i) * (c j * x a ^ j))
        = ∑ i ∈ range n, ∑ a ∈ s, ∑ j ∈ range n, w a * (ρ - x a) * ((c i * x a ^ i) * (c j * x a ^ j)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ a ∈ s, ∑ i ∈ range n, ∑ j ∈ range n, w a * (ρ - x a) * ((c i * x a ^ i) * (c j * x a ^ j)) :=
          Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  rw [hsum]
  exact Finset.sum_nonneg fun a ha =>
    mul_nonneg (mul_nonneg (hw a ha) (by linarith [hxρ a ha])) (sq_nonneg _)

end Chain

/-! ## 4. The half-turn: one rotation of the sphere exchanges the two pictures -/

/-- The half-turn's matrix `(1/√2) [[−1, 1], [1, 1]]`. -/
def halfTurn : Matrix (Fin 2) (Fin 2) ℝ := !![-(1 / √2), 1 / √2; 1 / √2, 1 / √2]

theorem inv_sqrt_two_sq : (1 / √2) * (1 / √2) = (1 : ℝ) / 2 := by
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]

/-- **The half-turn is symmetric.** -/
theorem halfTurn_transpose : halfTurn.transpose = halfTurn := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [halfTurn]

/-- **The half-turn is an involution**, hence (being symmetric) orthogonal: a rotation of the sphere up to phase. -/
theorem halfTurn_mul_self : halfTurn * halfTurn = 1 := by
  have h : (√2)⁻¹ * (√2)⁻¹ = (1 : ℝ) / 2 := by rw [← one_div, inv_sqrt_two_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [halfTurn, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- **Its Moebius action is the electric profile.** -/
theorem halfTurn_mobius (c : ℝ) :
    (halfTurn 0 0 * c + halfTurn 0 1) / (halfTurn 1 0 * c + halfTurn 1 1) = elec c := by
  have hs : (0 : ℝ) < √2 := by positivity
  simp only [halfTurn, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  unfold elec
  rw [show -(1 / √2) * c + 1 / √2 = (1 - c) / √2 by ring, show 1 / √2 * c + 1 / √2 = (1 + c) / √2 by ring,
    div_div_div_cancel_right₀ hs.ne']

/-- **The second fixed point** `−(1 + √2)`. -/
theorem elec_fixed_neg : elec (-(1 + √2)) = -(1 + √2) := by
  have hs : (0 : ℝ) < √2 := by positivity
  unfold elec
  rw [div_eq_iff (by intro h; linarith)]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- **The two fixed points are antipodal on the sphere**: `−1/conj(√2 − 1) = −(1 + √2)`. -/
theorem fixed_antipodal : -(1 / (√2 - 1)) = -(1 + √2) := by
  rw [neg_inj, div_eq_iff sqrt_two_sub_one_pos.ne', mul_comm]
  exact sqrt_two_mul.symm

/-! ## 5. The hyperbolic ledger: costs add along the chain, the half-turn swaps the two compositions -/

/-- **The electric cost is the Poincare distance from the lossless point**: `−log elec c = log((1 + c)/(1 − c))`. -/
theorem elec_cost (c : ℝ) : -Real.log (elec c) = Real.log ((1 + c) / (1 - c)) := by
  unfold elec
  rw [← Real.log_inv, inv_div]

/-- **The Szego factor is a function of the electric factor**: `szego c = 4 f/(1 + f)²` with `f = elec c`. -/
theorem szego_of_elec {c : ℝ} (h : c ≠ -1) : szego c = 4 * elec c / (1 + elec c) ^ 2 := by
  have h' : 1 + c ≠ 0 := fun h0 => h (by linarith)
  have h2 : 1 + (1 - c) / (1 + c) = 2 / (1 + c) := by field_simp; ring
  unfold szego
  rw [Real.norm_eq_abs, sq_abs, elec, h2]
  field_simp
  ring

/-- **Series composition**: under `a ⊕ b = (a + b)/(1 + a b)` the electric factors multiply (the costs add). -/
theorem elec_oplus {a b : ℝ} (ha : 1 + a ≠ 0) (hb : 1 + b ≠ 0) (hab : 1 + a * b ≠ 0) :
    elec ((a + b) / (1 + a * b)) = elec a * elec b := by
  unfold elec
  rw [one_sub_div hab, one_add_div hab, div_div_div_cancel_right₀ hab, div_mul_div_comm,
    div_eq_div_iff (by intro h0; apply mul_ne_zero ha hb; linear_combination h0) (mul_ne_zero ha hb)]
  ring

/-- **The half-turn swaps the two compositions**: the product of reflection coefficients (parallel) is carried to the
`⊕` of electric factors (series). -/
theorem elec_mul {a b : ℝ} (ha : 1 + a ≠ 0) (hb : 1 + b ≠ 0) (hab : 1 + a * b ≠ 0) :
    elec (a * b) = (elec a + elec b) / (1 + elec a * elec b) := by
  have hd : (1 + a) * (1 + b) + (1 - a) * (1 - b) ≠ 0 := by
    intro h0; apply hab; linear_combination h0 / 2
  unfold elec
  rw [div_add_div _ _ ha hb, div_mul_div_comm, one_add_div (mul_ne_zero ha hb),
    div_div_div_cancel_right₀ (mul_ne_zero ha hb),
    div_eq_div_iff (by intro h0; apply hab; linarith) (by intro h0; apply hd; linear_combination h0)]
  ring

/-- **Two lossless hand-over steps fall short of the one-box floor**: `(√2 − 1)² > 1/μ` for `μ ≥ 6`. -/
theorem two_steps_short {μ : ℝ} (hμ : 6 ≤ μ) : 1 < (√2 - 1) ^ 2 * μ := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hlt : 12 * √2 < 17 := by nlinarith
  have hpos : 1 < (√2 - 1) ^ 2 * 6 := by nlinarith
  have hsq : 0 ≤ (√2 - 1) ^ 2 := sq_nonneg _
  nlinarith

/-- **Three lossless hand-over steps clear it**: `(√2 − 1)³ < 1/μ` for `μ ≤ 14`. -/
theorem three_steps_clear {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ 14) : (√2 - 1) ^ 3 * μ < 1 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hcube : (√2 - 1) ^ 3 = 5 * √2 - 7 := by nlinarith
  have hlt : 70 * √2 < 99 := by nlinarith
  have hpos : 0 < 5 * √2 - 7 := by nlinarith
  rw [hcube]
  nlinarith

/-! ## 6. The two-boundary pairing has the same kind of involution -/

/-- A separator for the split `A(x, y) ∧ B(x, z)`: true wherever `A` can hold, false wherever `B` can. -/
def Separates {X Y Z : Type*} (A : X → Y → Prop) (B : X → Z → Prop) (I : X → Prop) : Prop :=
  (∀ x y, A x y → I x) ∧ ∀ x z, B x z → ¬ I x

/-- **Swapping the two sides negates the separator**: the involution exchanges the pictures and leaves the size of the
separator unchanged up to one negation, so it cannot create a cost. -/
theorem separates_swap {X Y Z : Type*} {A : X → Y → Prop} {B : X → Z → Prop} {I : X → Prop}
    (h : Separates A B I) : Separates B A fun x => ¬ I x :=
  ⟨fun x z hz => h.2 x z hz, fun x y hy hn => hn (h.1 x y hy)⟩

/-! ## 7. The twist form of O1 and the two-box encoder -/

/-- **O1 in its dual (twist) form**: the electric factor is at most `1/μ` exactly when the twist free energy
`F_tw = −log c` is at most `log((μ + 1)/(μ − 1))` (`0.297` for `μ₄ = 6.77`). -/
theorem oneBox_twist_form {c μ : ℝ} (h0 : 0 < c) (h1 : c < 1) (hμ : 1 < μ) :
    elec c ≤ μ⁻¹ ↔ -Real.log c ≤ Real.log ((μ + 1) / (μ - 1)) := by
  have hμ0 : 0 < μ := by linarith
  have hinv0 : 0 < μ⁻¹ := inv_pos.2 hμ0
  have hb : 0 < elec μ⁻¹ := (elec_mem hinv0 (inv_lt_one_of_one_lt₀ hμ)).1
  have hx : 0 < (μ - 1) / (μ + 1) := div_pos (by linarith) (by linarith)
  have hinv : μ⁻¹ = elec (elec μ⁻¹) := (elec_elec (by linarith)).symm
  rw [hinv, elec_le_elec_iff (by linarith) (by linarith), elec_inv hμ0,
    show Real.log ((μ + 1) / (μ - 1)) = -Real.log ((μ - 1) / (μ + 1)) by rw [← Real.log_inv, inv_div],
    neg_le_neg_iff, Real.log_le_log_iff hx h0]

/-- **Two independent boxes side by side**: the reflection coefficient of the summed label is the product. -/
theorem xor_product {q₀ q₁ r₀ r₁ : ℝ} :
    ((q₀ * r₀ + q₁ * r₁) - (q₀ * r₁ + q₁ * r₀)) / ((q₀ + q₁) * (r₀ + r₁)) =
      ((q₀ - q₁) / (q₀ + q₁)) * ((r₀ - r₁) / (r₀ + r₁)) := by
  rw [div_mul_div_comm]
  congr 1
  ring

/-- **The two-box defect is a determinant**: for a joint law `p` of the two labels, the summed label's coefficient minus
the product of the two marginal coefficients is `4 (p₀₀ p₁₁ − p₀₁ p₁₀)/S²`; it vanishes exactly for independent boxes. -/
theorem twoBox_defect {p₀₀ p₀₁ p₁₀ p₁₁ : ℝ} (hS : p₀₀ + p₀₁ + p₁₀ + p₁₁ ≠ 0) :
    (p₀₀ + p₁₁ - p₀₁ - p₁₀) / (p₀₀ + p₀₁ + p₁₀ + p₁₁) -
        ((p₀₀ + p₀₁ - p₁₀ - p₁₁) / (p₀₀ + p₀₁ + p₁₀ + p₁₁)) * ((p₀₀ + p₁₀ - p₀₁ - p₁₁) / (p₀₀ + p₀₁ + p₁₀ + p₁₁)) =
      4 * (p₀₀ * p₁₁ - p₀₁ * p₁₀) / (p₀₀ + p₀₁ + p₁₀ + p₁₁) ^ 2 := by
  field_simp
  ring

end ProofPhase.Unified
