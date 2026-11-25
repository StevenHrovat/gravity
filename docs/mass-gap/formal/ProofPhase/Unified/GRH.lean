/-
The unified lossy-step theorem: the GRH instance (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/UNIFIED.md`, section 3.2.
-/

import ProofPhase.Unified.Ledger
import ProofPhase.GRH.Induction
import ProofPhase.GRH.Weil

/-!
# GRH as a lossy chain: scales are the steps, the margin factor is the price, the sign is the open step

Weil's form restricted to a grid of cells is a Toeplitz form (`GRH/Induction.lean`, `toepForm`). The steps are scales:
the section of size `k + 1` grows to size `k + 2` (the primes enter as impulses at the lags `log p`; `grh/INDUCTION.md`
0.4). The certificate carried is a **margin**: `Sec t k e` says that `e` is a lower bound of the section of size `k + 1`
(`e ≤ λ_min`). The price of a step is the factor by which the margin may shrink.

* `sec_zero`: the first section is certified by the mass `re t 0`.
* `sec_nonneg`, `toepForm_indicator`, `pos_of_sections`: a nonnegative margin at every scale makes every finite section
  positive.
* **`ScaleSign t`** (the named hypothesis, **open** beyond the finite model and the known proofs): the mass is
  nonnegative and every scale step carries the margin with a **nonnegative** factor (no step overdraws the margin).
* `scaleSign_iff`: `ScaleSign t` is exactly positivity of every section (so it is not vacuous: models with every zero
  on the line satisfy it, `atomic_toep_nonneg`).
* `grh_margin`: with positive factors `f k = e^{-c k}`, the margin at scale `n` is the mass times `e^{-Σ c}` (the
  survival reading of the ledger; the decay of the margin is harmless, `GRH/Transfer.lean`).
* **`grh_instance`**: in the finite model of zeros (`ZeroModel`: finitely many zeros `ρ = 1/2 + i γ`, closed under the
  functional equation, the grid moments their exponential sums), `ScaleSign` puts every zero on the line and makes Weil's
  pairing nonnegative on every finite exponential sum (`atoms_on_circle`, `weil_criterion_finite`). The only non-proved
  input is `ScaleSign`.

**Why `f ≥ 0` and not `f > 0`.** In a finite model the sections of size above the number of zeros are singular, so the
factors vanish from there on: the ledger terminates. "No factor vanishes" is the infinite-zero case. No axioms beyond the
standard ones.
-/

open Finset ComplexConjugate Complex

noncomputable section

namespace ProofPhase.Unified

open ProofPhase.GRH

/-- **A certified margin**: `e` is a lower bound of the Toeplitz section of size `k + 1` of the moments `t`. -/
def Sec (t : ℤ → ℂ) (k : ℕ) (e : ℝ) : Prop :=
  ∀ c : ℕ → ℂ, e * ∑ j ∈ range (k + 1), ‖c j‖ ^ 2 ≤ (toepForm t (range (k + 1)) c).re

/-- The first section (one cell) is certified by the mass `re t 0`. -/
theorem sec_zero (t : ℤ → ℂ) : Sec t 0 (t 0).re := by
  intro c
  have h : toepForm t (range 1) c = ((‖c 0‖ ^ 2 : ℝ) : ℂ) * t 0 := by
    simp only [toepForm, range_one, sum_singleton, Nat.cast_zero, sub_zero]
    rw [Complex.conj_mul', Complex.ofReal_pow]
  rw [h, Complex.re_ofReal_mul, range_one, sum_singleton, mul_comm]

/-- A nonnegative certified margin makes the section positive. -/
theorem sec_nonneg {t : ℤ → ℂ} {k : ℕ} {e : ℝ} (h : Sec t k e) (he : 0 ≤ e) (c : ℕ → ℂ) :
    0 ≤ (toepForm t (range (k + 1)) c).re :=
  (mul_nonneg he (sum_nonneg fun j _ => sq_nonneg _)).trans (h c)

/-- A form on a smaller set of cells is the form on a larger one, with the vector extended by zero. -/
theorem toepForm_indicator (t : ℤ → ℂ) {s r : Finset ℕ} (hsr : s ⊆ r) (c : ℕ → ℂ) :
    toepForm t r (fun j => if j ∈ s then c j else 0) = toepForm t s c := by
  unfold toepForm
  rw [← Finset.sum_subset hsr]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.sum_subset hsr]
    · exact Finset.sum_congr rfl fun l hl => by simp [hj, hl]
    · intro l _ hl
      simp [hl]
  · intro j _ hj
    simp [hj]

/-- Positivity of the sections `range (k + 1)` gives positivity on every finite set of cells. -/
theorem pos_of_sections {t : ℤ → ℂ} (h : ∀ k (c : ℕ → ℂ), 0 ≤ (toepForm t (range (k + 1)) c).re)
    (s : Finset ℕ) (c : ℕ → ℂ) : 0 ≤ (toepForm t s c).re := by
  have hs : s ⊆ range (s.sup id + 1) := fun j hj =>
    mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
  rw [← toepForm_indicator t hs c]
  exact h _ _

/-- **The sign (GRH's named hypothesis).** The mass is nonnegative, and every scale step carries every certified margin
`e` to the certified margin `f k * e` with a nonnegative factor `f k`: no step overdraws the margin. -/
def ScaleSign (t : ℤ → ℂ) : Prop :=
  0 ≤ (t 0).re ∧ ∃ f : ℕ → ℝ, (∀ k, 0 ≤ f k) ∧ ∀ k e, Sec t k e → Sec t (k + 1) (f k * e)

/-- **The ledger at every scale**: under the sign, the margin at scale `n` is the mass times the product of the factors,
and it is nonnegative. -/
theorem scaleSign_margin {t : ℤ → ℂ} (h : ScaleSign t) :
    ∃ f : ℕ → ℝ, (∀ k, 0 ≤ f k) ∧ ∀ n, Sec t n ((∏ k ∈ range n, f k) * (t 0).re) := by
  obtain ⟨_, f, hf0, hf⟩ := h
  exact ⟨f, hf0, fun n => carry (fun k _ e he => hf k e he) (sec_zero t)⟩

/-- **The sign is positivity at every scale** (so `ScaleSign` is exactly the open statement, and not vacuous). -/
theorem scaleSign_iff (t : ℤ → ℂ) :
    ScaleSign t ↔ 0 ≤ (t 0).re ∧ ∀ k (c : ℕ → ℂ), 0 ≤ (toepForm t (range (k + 1)) c).re := by
  constructor
  · intro h
    obtain ⟨f, hf0, hm⟩ := scaleSign_margin h
    exact ⟨h.1, fun k => sec_nonneg (hm k) (mul_nonneg (prod_nonneg fun i _ => hf0 i) h.1)⟩
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun _ => 0, fun _ => le_rfl, fun k e _ c => ?_⟩
    rw [zero_mul, zero_mul]
    exact h (k + 1) c

/-- **The margin in costs**: with positive factors `f k = e^{-c k}`, `c k = -log f k`, the margin at scale `n` is the
mass times `e^{-Σ c}`. -/
theorem grh_margin {t : ℤ → ℂ} {f : ℕ → ℝ} (hf : ∀ k, 0 < f k) (h : ∀ k e, Sec t k e → Sec t (k + 1) (f k * e))
    (n : ℕ) : Sec t n (Real.exp (-∑ k ∈ range n, -Real.log (f k)) * (t 0).re) := by
  rw [← prod_eq_exp_neg_cost hf]
  exact carry (fun k _ e he => h k e he) (sec_zero t)

/-- **The finite model of zeros.** Finitely many zeros `ρ_i = 1/2 + i γ_i`, closed under `γ ↦ conj γ` (functional
equation and conjugation, via `σ`); on a grid of width `ε` they are the atoms `z_i = e^{i γ_i ε}` (distinct), with
non-zero weights; `t` is the moment sequence of Weil's form on the grid (Hermitian), whose moments are the atoms'
exponential sums. -/
structure ZeroModel (k : ℕ) where
  γ : Fin k → ℂ
  σ : Fin k → Fin k
  hσ : ∀ i, γ (σ i) = conj (γ i)
  ε : ℝ
  hε : 0 < ε
  hinj : Function.Injective fun i => Complex.exp (I * γ i * ε)
  w : Fin k → ℂ
  hw : ∀ i, w i ≠ 0
  t : ℤ → ℂ
  ht : ∀ m, t (-m) = conj (t m)
  hmom : ∀ n : ℕ, t n = ∑ i, w i * Complex.exp (I * γ i * ε) ^ n

/-- **The GRH instance.** In the finite model, the sign at every scale puts every zero on the line, and Weil's pairing
is nonnegative on every finite exponential sum. The only non-proved input is `ScaleSign`. -/
theorem grh_instance {k : ℕ} (Z : ZeroModel k) (h : ScaleSign Z.t) :
    (∀ i, (Z.γ i).im = 0) ∧ ∀ F ∈ expSums, 0 ≤ (weilSum Z.γ Z.σ F).re := by
  have hpos : ∀ s c, 0 ≤ (toepForm Z.t s c).re := pos_of_sections ((scaleSign_iff Z.t).1 h).2
  have hmir : ∀ i, ∃ j, Complex.exp (I * Z.γ j * Z.ε) = (conj (Complex.exp (I * Z.γ i * Z.ε)))⁻¹ := by
    intro i
    refine ⟨Z.σ i, ?_⟩
    rw [Z.hσ i, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hcirc := atoms_on_circle (fun i => Complex.exp (I * Z.γ i * Z.ε)) Z.w Z.hinj Z.hw
    (fun i => Complex.exp_ne_zero _) hmir Z.t Z.ht Z.hmom hpos
  have hreal : ∀ i, (Z.γ i).im = 0 := by
    intro i
    have hi := hcirc i
    simp only [Complex.norm_exp] at hi
    have h0 : (I * Z.γ i * (Z.ε : ℂ)).re = 0 := by
      rw [← Real.exp_eq_one_iff]; exact hi
    simp [Complex.mul_re] at h0
    rcases h0 with h0 | h0
    · exact h0
    · exact absurd h0 Z.hε.ne'
  exact ⟨hreal, (weil_criterion_finite Z.hσ).1 hreal⟩

end ProofPhase.Unified
