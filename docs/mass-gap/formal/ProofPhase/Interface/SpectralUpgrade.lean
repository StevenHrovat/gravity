/-
Proof phase, M1 task R12: the spectral upgrade (dense-class decay to uniform decay). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-r11/NOTE.md`, section R12.
-/

import Mathlib

/-!
# From decay on a dense class to uniform decay (reflection positivity, no spectral theorem)

Abstract setting: a real inner product space `H`, a bounded operator `T` that is symmetric and positive, a subspace `H0`
(for example the orthogonal complement of the vacuum) that `T` leaves invariant, and a set `D ⊆ H0` that is dense in `H0`.

**Hypothesis.** For every `G ∈ D` there is a constant `C_G` with `⟪G, T^n G⟫ ≤ C_G e^{-m n}` for all `n`.

**Conclusion.** `⟪F, T^n F⟫ ≤ e^{-m n} ‖F‖²` for every `F ∈ H0` and every `n`, `‖T^n F‖ ≤ e^{-m n} ‖F‖`, and
`|⟪F, T^n G⟫| ≤ e^{-m n} ‖F‖ ‖G‖` for `F, G ∈ H0`.

The proof is elementary. Positivity and symmetry give Cauchy-Schwarz for the forms `⟪x, y⟫` and `⟪x, T y⟫`, hence the
log-convexity `a_{k+1}² ≤ a_k a_{k+2}` of `a_k = ⟪G, T^k G⟫`. A log-convex sequence satisfies `a_n ≥ a_0 r^n` with
`r = a_1 / a_0`, so decay at rate `m` forces `r ≤ e^{-m}`: `⟪G, T G⟫ ≤ e^{-m} ‖G‖²` on `D`. This passes to the closure
of `D` by continuity. Finally a positive symmetric form bounded by `q ‖·‖²` on an invariant subspace bounds the operator
norm by `q` there, which iterates. Neither completeness of `H`, nor `‖T‖ ≤ 1`, nor the spectral theorem is used.
-/

open scoped RealInnerProductSpace

open Filter Topology

noncomputable section

namespace ProofPhase.Interface

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Cauchy-Schwarz for a symmetric positive operator (the form `(x, y) ↦ ⟪x, S y⟫`). -/
theorem psd_cauchy_schwarz (S : H →L[ℝ] H) (hsym : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫) (hpos : ∀ x, 0 ≤ ⟪x, S x⟫)
    (x y : H) : ⟪x, S y⟫ ^ 2 ≤ ⟪x, S x⟫ * ⟪y, S y⟫ := by
  have key : ∀ t : ℝ, 0 ≤ ⟪y, S y⟫ * (t * t) + (2 * ⟪x, S y⟫) * t + ⟪x, S x⟫ := by
    intro t
    have h := hpos (x + t • y)
    have e1 : ⟪y, S x⟫ = ⟪x, S y⟫ := by rw [← hsym, real_inner_comm]
    have e : ⟪x + t • y, S (x + t • y)⟫ =
        ⟪y, S y⟫ * (t * t) + (2 * ⟪x, S y⟫) * t + ⟪x, S x⟫ := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, e1,
        RCLike.conj_to_real]
      ring
    rwa [e] at h
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

variable (T : H →L[ℝ] H)

/-- `T^i` is symmetric if `T` is. -/
theorem pow_symm (hsym : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (i : ℕ) (x y : H) : ⟪(T ^ i) x, y⟫ = ⟪x, (T ^ i) y⟫ := by
  induction i generalizing x y with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, ih, hsym, ← ContinuousLinearMap.mul_apply, ← pow_succ']
    rfl

/-- The sequence `a_k = ⟪G, T^k G⟫`. -/
def moment (G : H) (k : ℕ) : ℝ := ⟪G, (T ^ k) G⟫

variable {T}

theorem moment_pairing (hsym : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (G : H) (i j : ℕ) :
    ⟪(T ^ i) G, (T ^ j) G⟫ = moment T G (i + j) := by
  unfold moment
  rw [pow_symm T hsym, ← ContinuousLinearMap.mul_apply, ← pow_add]

theorem moment_pairing_T (hsym : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (G : H) (i j : ℕ) :
    ⟪(T ^ i) G, T ((T ^ j) G)⟫ = moment T G (i + j + 1) := by
  unfold moment
  rw [pow_symm T hsym, ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← pow_succ, ← pow_add,
    add_right_comm]

/-- **Log-convexity** of the moments of a positive symmetric operator. -/
theorem moment_logconvex (hsym : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (hpos : ∀ x, 0 ≤ ⟪x, T x⟫) (G : H) (k : ℕ) :
    moment T G (k + 1) ^ 2 ≤ moment T G k * moment T G (k + 2) := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · -- k = 2m: the form ⟪x, y⟫ on T^m G, T^(m+1) G
    have h := psd_cauchy_schwarz (1 : H →L[ℝ] H) (fun x y => rfl) (fun x => real_inner_self_nonneg)
      ((T ^ m) G) ((T ^ (m + 1)) G)
    simp only [ContinuousLinearMap.one_apply] at h
    rw [moment_pairing hsym, moment_pairing hsym, moment_pairing hsym] at h
    have e1 : m + (m + 1) = 2 * m + 1 := by ring
    have e2 : m + m = 2 * m := by ring
    have e3 : m + 1 + (m + 1) = 2 * m + 2 := by ring
    rwa [e1, e2, e3] at h
  · -- k = 2m+1: the form ⟪x, T y⟫ on T^m G, T^(m+1) G
    have h := psd_cauchy_schwarz T hsym hpos ((T ^ m) G) ((T ^ (m + 1)) G)
    rw [moment_pairing_T hsym, moment_pairing_T hsym, moment_pairing_T hsym] at h
    have e1 : m + (m + 1) + 1 = 2 * m + 1 + 1 := by ring
    have e2 : m + m + 1 = 2 * m + 1 := by ring
    have e3 : m + 1 + (m + 1) + 1 = 2 * m + 1 + 2 := by ring
    rwa [e1, e2, e3] at h

theorem moment_nonneg (hsym : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (hpos : ∀ x, 0 ≤ ⟪x, T x⟫) (G : H) (k : ℕ) :
    0 ≤ moment T G k := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have := real_inner_self_nonneg (x := (T ^ m) G)
    rwa [moment_pairing hsym, ← two_mul] at this
  · have := hpos ((T ^ m) G)
    rw [moment_pairing_T hsym] at this
    have e : m + m + 1 = 2 * m + 1 := by ring
    rwa [e] at this

/-- A log-convex nonnegative sequence with `a₀, a₁ > 0` satisfies `a_{k+1} ≥ (a₁/a₀) a_k`. -/
theorem logconvex_ratio {a : ℕ → ℝ} (hlc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2)) (h0 : 0 < a 0) (h1 : 0 < a 1) :
    ∀ k, 0 < a k ∧ a 1 / a 0 * a k ≤ a (k + 1) := by
  intro k
  induction k with
  | zero =>
    refine ⟨h0, ?_⟩
    rw [div_mul_cancel₀ _ h0.ne']
  | succ k ih =>
    obtain ⟨hk, hr⟩ := ih
    set r := a 1 / a 0 with hr_def
    have hr0 : 0 < r := div_pos h1 h0
    have hk1 : 0 < a (k + 1) := lt_of_lt_of_le (mul_pos hr0 hk) hr
    have hc := hlc k
    have key : r * a (k + 1) ≤ a (k + 2) := by
      -- a_k a_{k+2} ≥ a_{k+1}^2 ≥ r a_k a_{k+1}
      have h2 : r * a k * a (k + 1) ≤ a (k + 1) ^ 2 := by nlinarith
      have h3 : a k * (r * a (k + 1)) ≤ a k * a (k + 2) := by nlinarith
      exact le_of_mul_le_mul_left h3 hk
    exact ⟨hk1, key⟩

/-- **Step 1.** Decay at rate `m` with some constant forces `⟪G, T G⟫ ≤ e^{-m} ‖G‖²`. -/
theorem inner_le_of_moment_decay (hsym : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (hpos : ∀ x, 0 ≤ ⟪x, T x⟫) (G : H)
    (m C : ℝ) (hdec : ∀ n : ℕ, ⟪G, (T ^ n) G⟫ ≤ C * Real.exp (-(m * n))) :
    ⟪G, T G⟫ ≤ Real.exp (-m) * ‖G‖ ^ 2 := by
  have h0e : moment T G 0 = ‖G‖ ^ 2 := by simp [moment]
  have h1e : moment T G 1 = ⟪G, T G⟫ := by simp [moment]
  have hq : 0 < Real.exp (-m) := Real.exp_pos _
  have hn0 := moment_nonneg hsym hpos G 0
  have hn1 := moment_nonneg hsym hpos G 1
  rcases hn0.eq_or_lt with h0 | h0
  · -- a_0 = 0: then G = 0
    have hG : G = 0 := by
      have : ‖G‖ ^ 2 = 0 := by rw [← h0e, ← h0]
      exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp this)
    subst hG; simp
  rcases hn1.eq_or_lt with h1 | h1
  · rw [← h1e, ← h1]; positivity
  -- generic case
  set a := moment T G with ha
  have hlc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2) := fun k => moment_logconvex hsym hpos G k
  have hrat := logconvex_ratio hlc h0 h1
  set r := a 1 / a 0 with hr_def
  have hr0 : 0 < r := div_pos h1 h0
  have hgrow : ∀ n : ℕ, r ^ n * a 0 ≤ a n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := (hrat n).2
      calc r ^ (n + 1) * a 0 = r * (r ^ n * a 0) := by ring
        _ ≤ r * a n := by gcongr
        _ ≤ a (n + 1) := this
  -- r ≤ e^{-m}
  have hle : r ≤ Real.exp (-m) := by
    by_contra hcon
    rw [not_le] at hcon
    have hρ : 1 < r * Real.exp m := by
      have : Real.exp (-m) * Real.exp m = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos m]
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / a 0) hρ
    have h1 := hgrow n
    have h2 : a n ≤ C * Real.exp (-(m * n)) := hdec n
    have h3 : (r * Real.exp m) ^ n * a 0 ≤ C := by
      have e : Real.exp (-(m * n)) * Real.exp m ^ n = 1 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, show -(m * (n : ℝ)) + n * m = 0 by ring]; simp
      calc (r * Real.exp m) ^ n * a 0 = (r ^ n * a 0) * Real.exp m ^ n := by rw [mul_pow]; ring
        _ ≤ (C * Real.exp (-(m * n))) * Real.exp m ^ n := by
            exact mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
        _ = C := by rw [mul_assoc, e, mul_one]
    have : C / a 0 < (r * Real.exp m) ^ n := hn
    rw [div_lt_iff₀ h0] at this
    linarith
  rw [← h1e]
  have : a 1 = r * a 0 := by rw [hr_def]; field_simp
  rw [this, ← h0e]
  gcongr

/-- **Step 2.** The inequality `⟪F, T F⟫ ≤ q ‖F‖²` passes to the closure of a set where it holds. -/
theorem inner_le_closure (T : H →L[ℝ] H) (q : ℝ) (D : Set H)
    (hD : ∀ G ∈ D, ⟪G, T G⟫ ≤ q * ‖G‖ ^ 2) : ∀ F ∈ closure D, ⟪F, T F⟫ ≤ q * ‖F‖ ^ 2 := by
  have hcl : IsClosed {F : H | ⟪F, T F⟫ ≤ q * ‖F‖ ^ 2} := by
    apply isClosed_le
    · exact Continuous.inner continuous_id T.continuous
    · exact continuous_const.mul (continuous_norm.pow 2)
  exact closure_minimal hD hcl

/-- **Step 3.** On an invariant subspace, a bound `⟪F, T F⟫ ≤ q ‖F‖²` bounds the operator norm by `q`. -/
theorem norm_le_of_inner_le (hsym : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (hpos : ∀ x, 0 ≤ ⟪x, T x⟫) (H0 : Submodule ℝ H)
    (hinv : ∀ x ∈ H0, T x ∈ H0) {q : ℝ} (hq : 0 ≤ q) (hb : ∀ F ∈ H0, ⟪F, T F⟫ ≤ q * ‖F‖ ^ 2) :
    ∀ y ∈ H0, ‖T y‖ ≤ q * ‖y‖ := by
  intro y hy
  have hTy := hinv y hy
  have hcs := psd_cauchy_schwarz T hsym hpos (T y) y
  have h1 : ⟪T y, T (T y)⟫ ≤ q * ‖T y‖ ^ 2 := hb _ hTy
  have h2 : ⟪y, T y⟫ ≤ q * ‖y‖ ^ 2 := hb _ hy
  have h3 : ⟪T y, T y⟫ = ‖T y‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [h3] at hcs
  have hnn1 := hpos (T y)
  have hnn2 := hpos y
  have h4 : (‖T y‖ ^ 2) ^ 2 ≤ (q * ‖T y‖ * ‖y‖) ^ 2 := by
    calc (‖T y‖ ^ 2) ^ 2 ≤ ⟪T y, T (T y)⟫ * ⟪y, T y⟫ := hcs
      _ ≤ (q * ‖T y‖ ^ 2) * (q * ‖y‖ ^ 2) := mul_le_mul h1 h2 hnn2 (hnn1.trans h1)
      _ = (q * ‖T y‖ * ‖y‖) ^ 2 := by ring
  have h5 : ‖T y‖ ^ 2 ≤ q * ‖T y‖ * ‖y‖ :=
    le_of_sq_le_sq (by simpa using h4) (by positivity) |> fun h => by simpa using h
  by_cases hz : ‖T y‖ = 0
  · rw [hz]; positivity
  · have hpz : 0 < ‖T y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have : ‖T y‖ * ‖T y‖ ≤ (q * ‖y‖) * ‖T y‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpz

/-- Iterating a norm bound on an invariant subspace. -/
theorem iter_norm_bound (H0 : Submodule ℝ H) (hinv : ∀ x ∈ H0, T x ∈ H0) {q : ℝ} (hq : 0 ≤ q)
    (hnorm : ∀ y ∈ H0, ‖T y‖ ≤ q * ‖y‖) :
    ∀ n : ℕ, ∀ F ∈ H0, (T ^ n) F ∈ H0 ∧ ‖(T ^ n) F‖ ≤ q ^ n * ‖F‖ := by
  intro n
  induction n with
  | zero => intro F hF; simpa using hF
  | succ n ih =>
    intro F hF
    obtain ⟨h1, h2⟩ := ih F hF
    have e : (T ^ (n + 1)) F = T ((T ^ n) F) := by
      rw [pow_succ', ContinuousLinearMap.mul_apply]
    rw [e]
    refine ⟨hinv _ h1, ?_⟩
    calc ‖T ((T ^ n) F)‖ ≤ q * ‖(T ^ n) F‖ := hnorm _ h1
      _ ≤ q * (q ^ n * ‖F‖) := by gcongr
      _ = q ^ (n + 1) * ‖F‖ := by ring

theorem exp_neg_mul_nat (m : ℝ) (n : ℕ) : Real.exp (-(m * n)) = Real.exp (-m) ^ n := by
  rw [← Real.exp_nat_mul]; congr 1; ring

/-- **The spectral upgrade (abstract, elementary).** `T` bounded, symmetric, positive; `H0` a subspace invariant under `T`;
`D` a set whose closure contains `H0` (e.g. `D ⊆ H0` dense in `H0`). If every `G ∈ D` has `⟪G, T^n G⟫ ≤ C_G e^{-m n}` for all `n` (constant `C_G` depending on `G`,
rate `m` shared), then `⟪F, T^n F⟫ ≤ e^{-m n} ‖F‖²` for all `F ∈ H0` and all `n`. -/
theorem spectral_upgrade (hsym : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (hpos : ∀ x, 0 ≤ ⟪x, T x⟫) (H0 : Submodule ℝ H)
    (hinv : ∀ x ∈ H0, T x ∈ H0) (D : Set H) (hD : (H0 : Set H) ⊆ closure D) (m : ℝ)
    (hdec : ∀ G ∈ D, ∃ C : ℝ, ∀ n : ℕ, ⟪G, (T ^ n) G⟫ ≤ C * Real.exp (-(m * n))) :
    ∀ F ∈ H0, ∀ n : ℕ, ⟪F, (T ^ n) F⟫ ≤ Real.exp (-(m * n)) * ‖F‖ ^ 2 := by
  have hq : (0 : ℝ) ≤ Real.exp (-m) := (Real.exp_pos _).le
  have hD1 : ∀ G ∈ D, ⟪G, T G⟫ ≤ Real.exp (-m) * ‖G‖ ^ 2 := by
    intro G hG
    obtain ⟨C, hC⟩ := hdec G hG
    exact inner_le_of_moment_decay hsym hpos G m C hC
  have hcl := inner_le_closure T (Real.exp (-m)) D hD1
  have hH0 : ∀ F ∈ H0, ⟪F, T F⟫ ≤ Real.exp (-m) * ‖F‖ ^ 2 := fun F hF => hcl F (hD hF)
  have hnorm := norm_le_of_inner_le hsym hpos H0 hinv hq hH0
  have hiter := iter_norm_bound H0 hinv hq hnorm
  intro F hF n
  calc ⟪F, (T ^ n) F⟫ ≤ ‖F‖ * ‖(T ^ n) F‖ := real_inner_le_norm _ _
    _ ≤ ‖F‖ * (Real.exp (-m) ^ n * ‖F‖) := by gcongr; exact (hiter n F hF).2
    _ = Real.exp (-(m * n)) * ‖F‖ ^ 2 := by rw [exp_neg_mul_nat]; ring

/-- **The one-step form:** `⟪F, T F⟫ ≤ e^{-m} ‖F‖²` on `H0`. -/
theorem spectral_upgrade_step (hsym : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (hpos : ∀ x, 0 ≤ ⟪x, T x⟫) (H0 : Submodule ℝ H)
    (hinv : ∀ x ∈ H0, T x ∈ H0) (D : Set H) (hD : (H0 : Set H) ⊆ closure D) (m : ℝ)
    (hdec : ∀ G ∈ D, ∃ C : ℝ, ∀ n : ℕ, ⟪G, (T ^ n) G⟫ ≤ C * Real.exp (-(m * n))) :
    ∀ F ∈ H0, ⟪F, T F⟫ ≤ Real.exp (-m) * ‖F‖ ^ 2 := by
  intro F hF
  have := spectral_upgrade hsym hpos H0 hinv D hD m hdec F hF 1
  simpa using this

/-- **The norm and cross forms:** `‖T^n G‖ ≤ e^{-m n} ‖G‖` and `|⟪F, T^n G⟫| ≤ e^{-m n} ‖F‖ ‖G‖` for `F, G ∈ H0`. -/
theorem spectral_upgrade_cross (hsym : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (hpos : ∀ x, 0 ≤ ⟪x, T x⟫) (H0 : Submodule ℝ H)
    (hinv : ∀ x ∈ H0, T x ∈ H0) (D : Set H) (hD : (H0 : Set H) ⊆ closure D) (m : ℝ)
    (hdec : ∀ G ∈ D, ∃ C : ℝ, ∀ n : ℕ, ⟪G, (T ^ n) G⟫ ≤ C * Real.exp (-(m * n))) :
    ∀ F ∈ H0, ∀ G ∈ H0, ∀ n : ℕ,
      ‖(T ^ n) G‖ ≤ Real.exp (-(m * n)) * ‖G‖ ∧ |⟪F, (T ^ n) G⟫| ≤ Real.exp (-(m * n)) * (‖F‖ * ‖G‖) := by
  have hstep := spectral_upgrade_step hsym hpos H0 hinv D hD m hdec
  have hnorm := norm_le_of_inner_le hsym hpos H0 hinv (Real.exp_pos (-m)).le hstep
  have hiter := iter_norm_bound H0 hinv (Real.exp_pos (-m)).le hnorm
  intro F hF G hG n
  have hb : ‖(T ^ n) G‖ ≤ Real.exp (-(m * n)) * ‖G‖ := by
    rw [exp_neg_mul_nat]; exact (hiter n G hG).2
  refine ⟨hb, ?_⟩
  calc |⟪F, (T ^ n) G⟫| ≤ ‖F‖ * ‖(T ^ n) G‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖F‖ * (Real.exp (-(m * n)) * ‖G‖) := by gcongr
    _ = Real.exp (-(m * n)) * (‖F‖ * ‖G‖) := by ring

end Abstract

end ProofPhase.Interface
