/-
Closures round (2026-11-24): the chain criterion and the tube threshold, stated jointly. Released under Apache 2.0.

Paper: Part III, III.5.6 care point 2 (claim III.5.8); `docs/paper/OPEN-CLAIMS-CLOSURES.md`.
-/

import ProofPhase.Crossover.CompositeHTF
import ProofPhase.Crossover.Containment

/-!
# The chain criterion and the tube threshold: neither implies the other; the joint form gives both

**Claim level.** Lean, in the abstract transfer-matrix model of `Crossover/CompositeHTF.lean` (a nonnegative flux
spectrum `Z₁`, submultiplicative; a neutral sector `Z₀ ≥ lⁿ`; the flux free energy `F n = log Z₀ n − log Z₁ n` and the
excess act `c n = log (Z₀ n / lⁿ)`). The identification with SU(2) is the one of that file and is not re-derived.

* **Chain criterion** (III.3.4): `F(L) > 2 c(L)`; with `c ≤ C` on the multiples of `L` the chain multiplies,
  `F(kL) ≥ k (F(L) − 2C)` (`flux_superadd_iter`).
* **Tube threshold** (III.5.4): `F > log μ`, the per-box cost above the path entropy (`tube_threshold`).

The theorems.
* `joint_gives_both` (S): **the joint form** `F(L) − 2C > log μ` (with `μ ≥ 1` continuations) gives both criteria, and the multiplied path sum
  `μ^k e^{−F(kL)}` decays geometrically at rate `F(L) − 2C − log μ` and is summable over `k ≥ 1`.
* `tube_not_chain` (S): a model in which the tube threshold holds at `L = 1` (`F(1) = 11 > log 7`) and the chain
  criterion fails (`F(1) = 11 ≤ 2 c(1) = 20`).
* `chain_not_tube` (S): a model in which the chain criterion holds (`F(1) = 1 > 2 c(1) = 0`) and the tube threshold fails
  (`F(1) = 1 < log 7`).

So in the model neither criterion follows from the other, and the one statement that gives both is the joint one:
the per-box cost **after** the excess act exceeds the path entropy. What the cubic geometry adds (paths that turn, not
one transfer direction) is not in the model; it is carried by O1's per-outside form (`Closures/OneBoxForm.lean`).
-/

open Real

namespace ProofPhase.Closures.ChainJoint

/-- The flux free energy of the model. -/
noncomputable def F (Z₀ Z₁ : ℕ → ℝ) (n : ℕ) : ℝ := Real.log (Z₀ n) - Real.log (Z₁ n)

/-- The excess act of the model. -/
noncomputable def c (Z₀ : ℕ → ℝ) (l : ℝ) (n : ℕ) : ℝ := Real.log (Z₀ n / l ^ n)

/-- **The joint form gives both criteria and the multiplied path sum** (S). -/
theorem joint_gives_both {Z₀ Z₁ : ℕ → ℝ} {l μ C : ℝ} (hl : 0 < l) (h1 : ∀ n, 0 < Z₁ n) (h0 : ∀ n, l ^ n ≤ Z₀ n)
    (hsub : ∀ a b, Z₁ (a + b) ≤ Z₁ a * Z₁ b) (L : ℕ) (hC0 : 0 ≤ C) (hC : ∀ k, c Z₀ l (k * L) ≤ C) (hμ1 : 1 ≤ μ)
    (hjoint : Real.log μ < F Z₀ Z₁ L - 2 * C) :
    2 * c Z₀ l L < F Z₀ Z₁ L ∧ μ * Real.exp (-F Z₀ Z₁ L) < 1 ∧
      (∀ k : ℕ, 1 ≤ k →
        μ ^ k * Real.exp (-F Z₀ Z₁ (k * L)) ≤ Real.exp (-(k * (F Z₀ Z₁ L - 2 * C - Real.log μ)))) ∧
      Summable (fun k : ℕ => μ ^ (k + 1) * Real.exp (-F Z₀ Z₁ ((k + 1) * L))) := by
  have hμ : 0 < μ := by linarith
  have hlog0 : 0 ≤ Real.log μ := Real.log_nonneg hμ1
  have hcL : c Z₀ l L ≤ C := by simpa using hC 1
  have hiter : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * (F Z₀ Z₁ L - 2 * C) ≤ F Z₀ Z₁ (k * L) := fun k hk =>
    ProofPhase.Crossover.flux_superadd_iter hl h1 h0 hsub L hC0 hC hk
  have hlogμ : Real.log μ < F Z₀ Z₁ L := by linarith
  have hbound : ∀ k : ℕ, 1 ≤ k →
      μ ^ k * Real.exp (-F Z₀ Z₁ (k * L)) ≤ Real.exp (-(k * (F Z₀ Z₁ L - 2 * C - Real.log μ))) := by
    intro k hk
    have hμk : μ ^ k = Real.exp (k * Real.log μ) := by
      rw [← Real.exp_log (pow_pos hμ k), Real.log_pow]
    rw [hμk, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have := hiter k hk
    nlinarith
  refine ⟨by linarith, (ProofPhase.Crossover.tube_threshold hμ _).2 hlogμ, hbound, ?_⟩
  set r := F Z₀ Z₁ L - 2 * C - Real.log μ with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hgeom : Summable (fun k : ℕ => Real.exp (-r) ^ (k + 1)) := by
    have hq : Real.exp (-r) < 1 := by
      have h := Real.exp_lt_exp.2 (show -r < 0 by linarith)
      rwa [Real.exp_zero] at h
    exact (summable_geometric_of_lt_one (Real.exp_pos _).le hq).comp_injective (add_left_injective 1)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hgeom
  have hb := hbound (k + 1) (by omega)
  have he : Real.exp (-(((k + 1 : ℕ) : ℝ) * r)) = Real.exp (-r) ^ (k + 1) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc μ ^ (k + 1) * Real.exp (-F Z₀ Z₁ ((k + 1) * L)) ≤ Real.exp (-(((k + 1 : ℕ) : ℝ) * r)) := by
        simpa [hr] using hb
    _ = Real.exp (-r) ^ (k + 1) := he

/-- **The tube threshold does not give the chain criterion** (S): `Z₀ n = e^{10} eⁿ`, `Z₁ n = 1`, `l = e`; then
`F(1) = 11 > log 7` and `2 c(1) = 20 ≥ F(1)`. All hypotheses of the model hold. -/
theorem tube_not_chain :
    let Z₀ : ℕ → ℝ := fun n => Real.exp 10 * Real.exp 1 ^ n
    let Z₁ : ℕ → ℝ := fun _ => 1
    (∀ n, 0 < Z₁ n) ∧ (∀ n, Real.exp 1 ^ n ≤ Z₀ n) ∧ (∀ a b, Z₁ (a + b) ≤ Z₁ a * Z₁ b) ∧
      Real.log 7 < F Z₀ Z₁ 1 ∧ F Z₀ Z₁ 1 ≤ 2 * c Z₀ (Real.exp 1) 1 := by
  intro Z₀ Z₁
  have hF : F Z₀ Z₁ 1 = 11 := by
    simp only [F, Z₀, Z₁, pow_one, Real.log_one, sub_zero]
    rw [← Real.exp_add, Real.log_exp]; norm_num
  have hc : c Z₀ (Real.exp 1) 1 = 10 := by
    simp only [c, Z₀, pow_one]
    rw [mul_div_assoc, div_self (Real.exp_pos 1).ne', mul_one, Real.log_exp]
  refine ⟨fun _ => one_pos, fun n => ?_, fun _ _ => by simp [Z₁], ?_, ?_⟩
  · show Real.exp 1 ^ n ≤ Real.exp 10 * Real.exp 1 ^ n
    have h10 : 1 ≤ Real.exp 10 := Real.one_le_exp (by norm_num)
    nlinarith [pow_pos (Real.exp_pos 1) n]
  · rw [hF]
    have h7 : Real.log 7 < 11 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.add_one_le_exp (11 : ℝ)
      linarith
    exact h7
  · rw [hF, hc]; norm_num

/-- **The chain criterion does not give the tube threshold** (S): `Z₀ n = eⁿ`, `Z₁ n = 1`, `l = e`; then
`F(1) = 1 > 2 c(1) = 0` and `F(1) = 1 < log 7`. All hypotheses of the model hold. -/
theorem chain_not_tube :
    let Z₀ : ℕ → ℝ := fun n => Real.exp 1 ^ n
    let Z₁ : ℕ → ℝ := fun _ => 1
    (∀ n, 0 < Z₁ n) ∧ (∀ n, Real.exp 1 ^ n ≤ Z₀ n) ∧ (∀ a b, Z₁ (a + b) ≤ Z₁ a * Z₁ b) ∧
      2 * c Z₀ (Real.exp 1) 1 < F Z₀ Z₁ 1 ∧ F Z₀ Z₁ 1 < Real.log 7 := by
  intro Z₀ Z₁
  have hF : F Z₀ Z₁ 1 = 1 := by
    simp only [F, Z₀, Z₁, pow_one, Real.log_one, sub_zero, Real.log_exp]
  have hc : c Z₀ (Real.exp 1) 1 = 0 := by
    simp only [c, Z₀, pow_one]
    rw [div_self (Real.exp_pos 1).ne', Real.log_one]
  refine ⟨fun _ => one_pos, fun n => le_refl _, fun _ _ => by simp [Z₁], ?_, ?_⟩
  · rw [hF, hc]; norm_num
  · rw [hF, Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith

end ProofPhase.Closures.ChainJoint
