/-
Proof phase, cycle 2, workstream B (Conjecture S): one rate on generators gives one rate everywhere (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c2b-conjS/NOTE.md`, section 3.1.
-/

import Mathlib

/-!
# Rates on a generating set control the whole closed span, with no prefactor

Setting: a real inner product space `E` (for the application: the Osterwalder–Schrader Hilbert space of a limit theory,
restricted to the complement of the vacuum) and a **symmetric** bounded operator `T` (the one-step transfer matrix).
Nothing else is assumed: no positivity, no contraction, no completeness, no spectral theorem.

* `sq_le_mul_pow_two_mul`: `‖Tⁿx‖² ≤ ‖x‖ · ‖T²ⁿx‖` (Cauchy–Schwarz plus symmetry; the Hankel inequality).
* `le_of_doubling`: a real sequence `a ≥ 0` with `a(k)² ≤ a(0) a(2k)` that decays like `C e^{−mk}` for **some** constant
  `C` satisfies `a(n) ≤ a(0) e^{−mn}`: the doubling (Hankel) inequality removes every prefactor.
* `norm_pow_le_of_decay`: hence for one vector, `‖Tⁿx‖ ≤ C e^{−mn}` for some `C` implies `‖Tⁿx‖ ≤ e^{−mn} ‖x‖`.
* **`norm_pow_le_of_generators`** (headline): if every element `s` of a set `S` satisfies `‖Tᵏs‖ ≤ C_s e^{−mk}` with its
  own constant `C_s`, then **every** `v` in the closure of the linear span of `S` satisfies `‖Tⁿv‖ ≤ e^{−mn} ‖v‖`.
* `inner_pow_le_of_generators`: the covariance form `|⟨w, Tⁿv⟩| ≤ e^{−mn} ‖w‖ ‖v‖`.

**Use (paper, `NOTE.md` 3.1).** With `E` the OS space orthogonal to the vacuum and `S` the centred Wilson-loop vectors
(dense by the Giles-type generation theorem, `ProofPhase.SectorS.Loops` and the note), this says: the mass gap with rate
`m` holds as soon as **each single loop** has a connected autocorrelation decaying at rate `m`, with any loop-dependent
constant. The gap is decided on generators, and only their rates matter.

**Claim discipline.** Abstract functional analysis, true for every symmetric operator: group-blind, model-blind, and
satisfied by the photon (with `m = 0`) and by every gapped theory. It contains no Yang–Mills input. It is the infinite-
volume, operator form of what `ProofPhase.corr_le_of_decay` (Theorem C) does in finite volume with an additive error.
-/

open Real Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ProofPhase.SectorS

/-! ## A real lemma: doubling removes prefactors -/

/-- If all powers `x^(2^j)` stay below one bound, then `x ≤ 1`. -/
theorem le_one_of_pow_two_pow_bdd {x K : ℝ} (h : ∀ j : ℕ, x ^ (2 ^ j) ≤ K) : x ≤ 1 := by
  by_contra hle
  have hlt : 1 < x := lt_of_not_ge hle
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt K hlt
  have h1 : x ^ n ≤ x ^ (2 ^ n) := pow_le_pow_right₀ hlt.le (Nat.lt_two_pow_self).le
  linarith [h n]

/-- **The doubling inequality removes every prefactor.** A sequence `a ≥ 0` with `a(k)² ≤ a(0) a(2k)` for all `k` that
decays like `C e^{−mk}` (any constant `C`) satisfies `a(n) ≤ a(0) e^{−mn}` for every `n`. -/
theorem le_of_doubling {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hcs : ∀ k, a k ^ 2 ≤ a 0 * a (2 * k)) {C m : ℝ}
    (hdec : ∀ k, a k ≤ C * Real.exp (-(m * k))) (n : ℕ) : a n ≤ a 0 * Real.exp (-(m * n)) := by
  rcases (ha 0).lt_or_eq with h0 | h0
  · -- normalise: `b k = a k / a 0`, `b k ^ 2 ≤ b (2k)`
    set b : ℕ → ℝ := fun k => a k / a 0 with hb
    have hb0 : ∀ k, 0 ≤ b k := fun k => div_nonneg (ha k) h0.le
    have hbcs : ∀ k, b k ^ 2 ≤ b (2 * k) := by
      intro k
      simp only [hb, div_pow]
      rw [div_le_div_iff₀ (by positivity) h0, pow_two (a 0)]
      nlinarith [hcs k, h0]
    -- iterate: `b n ^ (2^j) ≤ b (2^j n)`
    have hit : ∀ j : ℕ, b n ^ (2 ^ j) ≤ b (2 ^ j * n) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc b n ^ (2 ^ (j + 1)) = (b n ^ (2 ^ j)) ^ 2 := by rw [pow_succ, pow_mul]
          _ ≤ b (2 ^ j * n) ^ 2 := pow_le_pow_left₀ (pow_nonneg (hb0 n) _) ih 2
          _ ≤ b (2 * (2 ^ j * n)) := hbcs _
          _ = b (2 ^ (j + 1) * n) := by rw [pow_succ]; ring_nf
    -- `y = b n e^{mn}` has bounded `2^j`-th powers
    set y := b n * Real.exp (m * n) with hy
    have hbound : ∀ j : ℕ, y ^ (2 ^ j) ≤ C / a 0 := by
      intro j
      have hdj : b (2 ^ j * n) ≤ C / a 0 * Real.exp (-(m * ((2 ^ j * n : ℕ) : ℝ))) := by
        simp only [hb]
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (hdec _) h0.le
      have e1 : y ^ (2 ^ j) = b n ^ (2 ^ j) * Real.exp (m * ((2 ^ j * n : ℕ) : ℝ)) := by
        rw [hy, mul_pow, ← Real.exp_nat_mul]
        congr 2; push_cast; ring
      rw [e1]
      calc b n ^ (2 ^ j) * Real.exp (m * ((2 ^ j * n : ℕ) : ℝ))
          ≤ C / a 0 * Real.exp (-(m * ((2 ^ j * n : ℕ) : ℝ))) * Real.exp (m * ((2 ^ j * n : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right ((hit j).trans hdj) (Real.exp_pos _).le
        _ = C / a 0 := by rw [mul_assoc, ← Real.exp_add]; simp
    have hy1 : y ≤ 1 := le_one_of_pow_two_pow_bdd hbound
    -- back to `a n`
    have : a n = a 0 * b n := by simp only [hb]; field_simp
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ h0.le
    have he := Real.exp_pos (m * n)
    calc b n = y * Real.exp (-(m * n)) := by
            rw [hy, mul_assoc, ← Real.exp_add]; simp
      _ ≤ 1 * Real.exp (-(m * n)) := mul_le_mul_of_nonneg_right hy1 (Real.exp_pos _).le
      _ = Real.exp (-(m * n)) := one_mul _
  · -- `a 0 = 0` forces `a n = 0`
    have h := hcs n
    rw [← h0, zero_mul] at h
    have : a n = 0 := by nlinarith [ha n]
    rw [this, ← h0, zero_mul]

/-! ## Symmetric operators -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `T` is **symmetric**: `⟨T x, y⟩ = ⟨x, T y⟩`. -/
def IsSymm (T : E →L[ℝ] E) : Prop := ∀ x y : E, ⟪T x, y⟫ = ⟪x, T y⟫

theorem IsSymm.pow {T : E →L[ℝ] E} (hT : IsSymm T) (n : ℕ) : IsSymm (T ^ n) := by
  induction n with
  | zero => intro x y; simp
  | succ n ih =>
    intro x y
    have e1 : (T ^ (n + 1)) x = (T ^ n) (T x) := by rw [pow_succ]; rfl
    have e2 : (T ^ (n + 1)) y = T ((T ^ n) y) := by rw [pow_succ']; rfl
    rw [e1, e2, ih, hT]

/-- **The Hankel inequality** `‖Tⁿx‖² ≤ ‖x‖ ‖T²ⁿx‖`. -/
theorem sq_le_mul_pow_two_mul {T : E →L[ℝ] E} (hT : IsSymm T) (n : ℕ) (x : E) :
    ‖(T ^ n) x‖ ^ 2 ≤ ‖x‖ * ‖(T ^ (2 * n)) x‖ := by
  rw [← real_inner_self_eq_norm_sq, hT.pow n]
  have : (T ^ n) ((T ^ n) x) = (T ^ (2 * n)) x := by rw [two_mul, pow_add]; rfl
  rw [this]
  exact real_inner_le_norm _ _

/-- **One vector:** exponential decay with some prefactor implies decay with prefactor `‖x‖`. -/
theorem norm_pow_le_of_decay {T : E →L[ℝ] E} (hT : IsSymm T) {x : E} {C m : ℝ}
    (hdec : ∀ k : ℕ, ‖(T ^ k) x‖ ≤ C * Real.exp (-(m * k))) (n : ℕ) :
    ‖(T ^ n) x‖ ≤ Real.exp (-(m * n)) * ‖x‖ := by
  have h := le_of_doubling (a := fun k => ‖(T ^ k) x‖) (fun k => norm_nonneg _)
    (fun k => by simpa using sq_le_mul_pow_two_mul hT k x) hdec n
  simpa [mul_comm] using h

/-- The vectors that decay at rate `m` with some prefactor form a submodule. -/
def decaySubmodule (T : E →L[ℝ] E) (m : ℝ) : Submodule ℝ E where
  carrier := {v | ∃ C : ℝ, ∀ k : ℕ, ‖(T ^ k) v‖ ≤ C * Real.exp (-(m * k))}
  zero_mem' := ⟨0, fun k => by simp⟩
  add_mem' := by
    rintro v w ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
    refine ⟨C₁ + C₂, fun k => ?_⟩
    rw [map_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ k) (h₂ k))
  smul_mem' := by
    rintro c v ⟨C, h⟩
    refine ⟨‖c‖ * C, fun k => ?_⟩
    rw [map_smul, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h k) (norm_nonneg _)

/-- **Headline: one rate on generators gives one rate on the closed span, with no prefactor.** If every `s ∈ S` has
`‖Tᵏs‖ ≤ C_s e^{−mk}` for all `k` (its own constant), then every `v` in the closure of `span S` has
`‖Tⁿv‖ ≤ e^{−mn}‖v‖` for all `n`. -/
theorem norm_pow_le_of_generators {T : E →L[ℝ] E} (hT : IsSymm T) {m : ℝ} {S : Set E}
    (hS : ∀ s ∈ S, ∃ C : ℝ, ∀ k : ℕ, ‖(T ^ k) s‖ ≤ C * Real.exp (-(m * k))) :
    ∀ v ∈ closure (Submodule.span ℝ S : Set E), ∀ n : ℕ, ‖(T ^ n) v‖ ≤ Real.exp (-(m * n)) * ‖v‖ := by
  intro v hv n
  have hspan : Submodule.span ℝ S ≤ decaySubmodule T m := Submodule.span_le.2 hS
  have hclosed : IsClosed {w : E | ‖(T ^ n) w‖ ≤ Real.exp (-(m * n)) * ‖w‖} :=
    isClosed_le (continuous_norm.comp (T ^ n).continuous) (continuous_const.mul continuous_norm)
  have hsub : (Submodule.span ℝ S : Set E) ⊆ {w : E | ‖(T ^ n) w‖ ≤ Real.exp (-(m * n)) * ‖w‖} := by
    intro w hw
    obtain ⟨C, hC⟩ := hspan hw
    exact norm_pow_le_of_decay hT hC n
  exact closure_minimal hsub hclosed hv

/-- **Covariance form:** under the same hypothesis, `|⟨w, Tⁿv⟩| ≤ e^{−mn} ‖w‖ ‖v‖` for every `w` and every `v` in the
closed span. -/
theorem inner_pow_le_of_generators {T : E →L[ℝ] E} (hT : IsSymm T) {m : ℝ} {S : Set E}
    (hS : ∀ s ∈ S, ∃ C : ℝ, ∀ k : ℕ, ‖(T ^ k) s‖ ≤ C * Real.exp (-(m * k)))
    {v : E} (hv : v ∈ closure (Submodule.span ℝ S : Set E)) (w : E) (n : ℕ) :
    |⟪w, (T ^ n) v⟫| ≤ Real.exp (-(m * n)) * ‖w‖ * ‖v‖ := by
  calc |⟪w, (T ^ n) v⟫| ≤ ‖w‖ * ‖(T ^ n) v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖w‖ * (Real.exp (-(m * n)) * ‖v‖) :=
        mul_le_mul_of_nonneg_left (norm_pow_le_of_generators hT hS v hv n) (norm_nonneg _)
    _ = Real.exp (-(m * n)) * ‖w‖ * ‖v‖ := by ring

/-- **The converse is trivial** (so the reduction loses nothing): a uniform bound on the closed span gives each
generator a prefactor `‖s‖`. -/
theorem generators_of_uniform {T : E →L[ℝ] E} {m : ℝ} {S : Set E}
    (h : ∀ v ∈ closure (Submodule.span ℝ S : Set E), ∀ n : ℕ, ‖(T ^ n) v‖ ≤ Real.exp (-(m * n)) * ‖v‖) :
    ∀ s ∈ S, ∃ C : ℝ, ∀ k : ℕ, ‖(T ^ k) s‖ ≤ C * Real.exp (-(m * k)) := fun s hs =>
  ⟨‖s‖, fun k => by
    rw [mul_comm]
    exact h s (subset_closure (Submodule.subset_span hs)) k⟩

end ProofPhase.SectorS
