/-
Proof phase, crossover workstream (c9a-crossover): the transfer round from P vs NP and GRH. The multi-sector duality floor,
and "it runs" as the shared formal form of the one-box statement and the GRH reductio (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/TRANSFER.md`.
-/

import ProofPhase.GRH.Tate

/-!
# Two channels multiply to `2ⁿ`; a strict contraction on the neutral sector is the Yang-Mills side of "it runs"

**1. The multi-sector duality** (TRANSFER.md 1). For `n` independent `ℤ/2` twist sectors, 't Hooft's Fourier relation gives
`(1 + S_tw)(1 + S_e) = 2ⁿ` (paper), with `S_tw = Σ_{k ≠ 0} Z(k)/Z(0)` the summed twist weight and `S_e = Σ_{e ≠ 0} Z_e(e)/Z_e(0)`
the summed electric weight. The two channels **multiply** to a constant, where the cutting-planes channels **add**.
* **`min_le_of_sector_product`** (S): `(1 + a)(1 + b) = 2ⁿ` ⟹ `min a b ≤ √(2ⁿ) − 1`.
* **`selfdual_sector_ge_one`** (S): for `n ≥ 2`, `√(2ⁿ) − 1 ≥ 1`. So for two or more sectors the duality allows both summed
  weights to be at least `1` (the self-dual point), and forces neither below `1`.
* **`electric_sum_lt_one_iff`** (S): with `(1 + a)(1 + b) = 2ⁿ`, `b < 1 ↔ 2^{n−1} < 1 + a`: summed electric weight below `1`
  exactly when the summed twist weight exceeds `2^{n−1} − 1` ('t Hooft's criterion, quantitative).

**2. "It runs", the Yang-Mills side** (TRANSFER.md 3), next to `runs_and_mirror_on_line` (`GRH/Tate.lean`):
* **`eig_norm_le_of_contraction`** (S): if `‖T x‖ ≤ η ‖x‖` on a set `S`, every eigenvector in `S` has `‖μ‖ ≤ η`.
* **`iterate_contraction`** (S): if moreover `T` maps `S` into itself, `‖Tⁿ x‖ ≤ ηⁿ ‖x‖` on `S`.
* **`no_phase_mode`** (S): with `η < 1`, no eigenvector in `S` has `‖μ‖ = 1`. GRH needs every mode to be a phase; the
  one-box statement needs no phase mode in the neutral sector.
-/

open ComplexConjugate

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Crossover

/-! ## 1. Multi-sector duality -/

/-- **The smaller summed weight is at most the self-dual value** (S). -/
theorem min_le_of_sector_product {a b : ℝ} {n : ℕ} (h : (1 + a) * (1 + b) = 2 ^ n) :
    min a b ≤ √(2 ^ n) - 1 := by
  by_contra hc'
  have hc : √(2 ^ n) - 1 < min a b := not_le.1 hc'
  have h1 : √(2 ^ n) - 1 < a := lt_of_lt_of_le hc (min_le_left a b)
  have h2 : √(2 ^ n) - 1 < b := lt_of_lt_of_le hc (min_le_right a b)
  have hs : √(2 ^ n) * √(2 ^ n) = 2 ^ n := Real.mul_self_sqrt (by positivity)
  have hs0 : 0 ≤ √(2 ^ n) := Real.sqrt_nonneg _
  have : √(2 ^ n) * √(2 ^ n) < (1 + a) * (1 + b) := by
    apply mul_lt_mul'' <;> linarith
  linarith

/-- **For two or more sectors the self-dual value is at least `1`** (S). -/
theorem selfdual_sector_ge_one {n : ℕ} (hn : 2 ≤ n) : 1 ≤ √(2 ^ n) - 1 := by
  have h4 : (4 : ℝ) ≤ 2 ^ n := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h44 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have := Real.sqrt_le_sqrt h4
  linarith

/-- **Summed electric weight below `1` iff summed twist weight above `2^{n−1} − 1`** (S). -/
theorem electric_sum_lt_one_iff {a b : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 1 ≤ n) (h : (1 + a) * (1 + b) = 2 ^ n) :
    b < 1 ↔ 2 ^ (n - 1) < 1 + a := by
  have hpos : 0 < 1 + a := by linarith
  have hb : 1 + b = 2 ^ n / (1 + a) := by field_simp; linarith
  have h2 : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  constructor
  · intro hlt
    have : 2 ^ n / (1 + a) < 2 := by linarith
    rw [div_lt_iff₀ hpos] at this
    linarith
  · intro hlt
    have : 2 ^ n / (1 + a) < 2 := by
      rw [div_lt_iff₀ hpos]
      linarith
    linarith

/-! ## 2. "It runs": strict contraction on the neutral sector -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- **Eigenvalues of a contraction on `S` are bounded by its rate** (S). -/
theorem eig_norm_le_of_contraction (T : V → V) {S : Set V} {η : ℝ} (hT : ∀ x ∈ S, ‖T x‖ ≤ η * ‖x‖) {μ : ℂ} {v : V}
    (hvS : v ∈ S) (hv : v ≠ 0) (h : T v = μ • v) : ‖μ‖ ≤ η := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have := hT v hvS
  rw [h, norm_smul] at this
  exact le_of_mul_le_mul_right this hv'

/-- **Iterated contraction** (S): `‖Tⁿ x‖ ≤ ηⁿ ‖x‖` on an invariant set. -/
theorem iterate_contraction (T : V → V) {S : Set V} {η : ℝ} (hη : 0 ≤ η) (hT : ∀ x ∈ S, ‖T x‖ ≤ η * ‖x‖)
    (hS : ∀ x ∈ S, T x ∈ S) (n : ℕ) : ∀ x ∈ S, ‖T^[n] x‖ ≤ η ^ n * ‖x‖ := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    have hmem : T^[n] x ∈ S := by
      clear ih
      induction n with
      | zero => simpa using hx
      | succ m ihm => rw [Function.iterate_succ_apply']; exact hS _ ihm
    calc ‖T (T^[n] x)‖ ≤ η * ‖T^[n] x‖ := hT _ hmem
      _ ≤ η * (η ^ n * ‖x‖) := mul_le_mul_of_nonneg_left (ih x hx) hη
      _ = η ^ (n + 1) * ‖x‖ := by ring

/-- **No phase mode under a strict contraction** (S): the Yang-Mills counterpart of `runs_and_mirror_on_line`. -/
theorem no_phase_mode (T : V → V) {S : Set V} {η : ℝ} (hη1 : η < 1) (hT : ∀ x ∈ S, ‖T x‖ ≤ η * ‖x‖) {μ : ℂ} {v : V}
    (hvS : v ∈ S) (hv : v ≠ 0) (h : T v = μ • v) : ‖μ‖ ≠ 1 := by
  have := eig_norm_le_of_contraction T hT hvS hv h
  intro h1
  linarith

/-- **The two halves side by side** (S): a norm-nonincreasing evolution with a mirror pair has the pair on the circle
(`runs_and_mirror_on_line`, GRH's target); a strict contraction on `S` has no eigenvector in `S` on the circle
(Yang-Mills's target). -/
theorem runs_two_targets (T : V → V) (hT : ∀ x, ‖T x‖ ≤ ‖x‖) {μ : ℂ} (hμ : μ ≠ 0) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0)
    (h1 : T v = μ • v) (h2 : T w = (conj μ)⁻¹ • w) {S : Set V} {η : ℝ} (hη1 : η < 1)
    (hS : ∀ x ∈ S, ‖T x‖ ≤ η * ‖x‖) : ‖μ‖ = 1 ∧ v ∉ S := by
  have hc := ProofPhase.GRH.runs_and_mirror_on_line T hT hμ hv hw h1 h2
  refine ⟨hc, fun hvS => no_phase_mode T hη1 hS hvS hv h1 hc⟩

end ProofPhase.Crossover
