/-
Proof phase, cycle 7, workstream b (c7b-centre): Griffiths' and Ginibre's inequalities for Ising-type (Z2) multi-spin models
with a finite family of interactions (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c7b-centre/NOTE.md`, section 2.
-/

import Mathlib

/-!
# Ginibre's inequality for Z2 (Ising-type) models, from scratch

**Model.** Sites `ι` (for a gauge theory: the links), spins `σ : ι → Bool` read as `±1` (`sgn`). A *monomial* of a finite
multiset `m` of sites is `mono σ m = ∏_{i ∈ m} sgn (σ i)` (a multiset, so a Wilson loop that visits a link twice is
allowed). An *interaction family* is a finite index type `κ` (for a gauge theory: the plaquettes) with a support
`supp k : Multiset ι` for each `k`; couplings `J : κ → ℝ`; energy `E_J(σ) = ∑_k J_k mono σ (supp k)`;
`Zf supp J = ∑_σ e^{E_J(σ)}`; `corr supp J B = (∑_σ mono σ B e^{E_J(σ)}) / Zf supp J`.

**Proved here (no hypotheses beyond the statements):**
* `gks1`: `0 ≤ ∑_σ mono σ B e^{E_c(σ)}` for `c ≥ 0` (Griffiths' first inequality), by expanding `e^{cx} = cosh c + sinh c · x`
  for `x = ±1` and `∑_σ mono σ m ≥ 0`;
* `ginibre`: `|J_k| ≤ K_k` for all `k` gives `corr J B ≤ corr K B` and `-corr J B ≤ corr K B`
  (Ginibre 1970), by two replicas `σ, τ = σρ`: the integrand becomes `mono σ B (1 ± mono ρ B) e^{∑ σ_k (K_k + J_k ρ_k)}` with
  non-negative coefficients, and `gks1` applies for every `ρ`. The same proof gives
* `griffiths2`: `corr c A * corr c B ≤ corr c (A + B)` for `c ≥ 0` (Griffiths' second inequality), and
* `corr_mono`: monotonicity of correlations in ferromagnetic couplings, `0 ≤ J ≤ K ⇒ corr J B ≤ corr K B` (a special case of
  `ginibre`, so no differentiation is needed).
* `abs_corr_le_abs`: `|corr J B| ≤ corr |J| B` for couplings of any sign: **the form F2 uses**.

Claim level: all theorems here are proved in Lean; nothing about SU(2).
-/

open Finset Real

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Centre

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The value `±1` of a spin (`false ↦ +1`, `true ↦ -1`, so that `xor` is the product). -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

theorem sgn_eq (b : Bool) : sgn b = 1 ∨ sgn b = -1 := by cases b <;> simp [sgn]

theorem sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by cases a <;> cases b <;> simp [sgn]

/-- Monomial of a multiset of sites: the product of the spins. -/
def mono (σ : ι → Bool) (m : Multiset ι) : ℝ := (m.map (fun i => sgn (σ i))).prod

theorem mono_add (σ : ι → Bool) (m₁ m₂ : Multiset ι) : mono σ (m₁ + m₂) = mono σ m₁ * mono σ m₂ := by
  simp [mono, Multiset.map_add, Multiset.prod_add]

theorem mono_zero (σ : ι → Bool) : mono σ 0 = 1 := by simp [mono]

theorem mono_sum {κ : Type*} [DecidableEq κ] (σ : ι → Bool) (supp : κ → Multiset ι) (S : Finset κ) :
    mono σ (∑ k ∈ S, supp k) = ∏ k ∈ S, mono σ (supp k) := by
  induction S using Finset.induction_on with
  | empty => simp [mono_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, mono_add, ih]

theorem mono_eq (σ : ι → Bool) (m : Multiset ι) : mono σ m = 1 ∨ mono σ m = -1 := by
  induction m using Multiset.induction_on with
  | empty => left; simp [mono]
  | cons a m ih =>
    have h : mono σ (a ::ₘ m) = sgn (σ a) * mono σ m := by simp [mono]
    rw [h]
    rcases sgn_eq (σ a) with h1 | h1 <;> rcases ih with h2 | h2 <;> rw [h1, h2] <;> simp

theorem mono_xor (σ ρ : ι → Bool) (m : Multiset ι) :
    mono (fun i => xor (σ i) (ρ i)) m = mono σ m * mono ρ m := by
  induction m using Multiset.induction_on with
  | empty => simp [mono]
  | cons a m ih =>
    have h : ∀ τ : ι → Bool, mono τ (a ::ₘ m) = sgn (τ a) * mono τ m := fun τ => by simp [mono]
    rw [h, h, h, ih, sgn_xor]; ring

theorem mono_eq_prod_pow (σ : ι → Bool) (m : Multiset ι) :
    mono σ m = ∏ i, sgn (σ i) ^ (m.count i) := by
  unfold mono
  rw [Finset.prod_multiset_map_count]
  refine Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => ?_)
  rw [Multiset.count_eq_zero.mpr (by simpa using hi)]; simp

/-- `∑_σ mono σ m ≥ 0` (it is `2^|ι|` if every site occurs an even number of times, and `0` otherwise). -/
theorem sum_mono_nonneg (m : Multiset ι) : 0 ≤ ∑ σ : ι → Bool, mono σ m := by
  have h : ∑ σ : ι → Bool, mono σ m = ∏ i, ∑ b : Bool, sgn b ^ (m.count i) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    · simp only [mono_eq_prod_pow]
  rw [h]
  refine Finset.prod_nonneg (fun i _ => ?_)
  have : ∑ b : Bool, sgn b ^ (m.count i) = 1 + (-1) ^ (m.count i) := by simp [sgn, add_comm]
  rw [this]
  rcases neg_one_pow_eq_or ℝ (m.count i) with h1 | h1 <;> rw [h1] <;> norm_num

/-! ## The model -/

section Model

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (supp : κ → Multiset ι)

/-- The energy `∑_k J_k mono σ (supp k)`. -/
def energy (J : κ → ℝ) (σ : ι → Bool) : ℝ := ∑ k, J k * mono σ (supp k)

/-- The partition function. -/
def Zf (J : κ → ℝ) : ℝ := ∑ σ : ι → Bool, exp (energy supp J σ)

/-- The unnormalised correlation of the monomial `B`. -/
def num (J : κ → ℝ) (B : Multiset ι) : ℝ := ∑ σ : ι → Bool, mono σ B * exp (energy supp J σ)

/-- The correlation `⟨σ_B⟩_J`. -/
def corr (J : κ → ℝ) (B : Multiset ι) : ℝ := num supp J B / Zf supp J

theorem Zf_pos (J : κ → ℝ) : 0 < Zf supp J := by
  unfold Zf
  exact Finset.sum_pos (fun σ _ => exp_pos _) Finset.univ_nonempty

theorem exp_mul_sign (c x : ℝ) (hx : x = 1 ∨ x = -1) : exp (c * x) = cosh c + sinh c * x := by
  rcases hx with rfl | rfl
  · rw [mul_one, mul_one, cosh_add_sinh]
  · rw [mul_neg_one, mul_neg_one, ← sub_eq_add_neg, cosh_sub_sinh, exp_neg]

/-- The Boltzmann factor as a sum over subsets of interactions. -/
theorem exp_energy_expand (c : κ → ℝ) (σ : ι → Bool) :
    exp (energy supp c σ) = ∑ S ∈ (univ : Finset κ).powerset,
      (∏ k ∈ univ \ S, cosh (c k)) * ∏ k ∈ S, (sinh (c k) * mono σ (supp k)) := by
  unfold energy
  rw [Real.exp_sum]
  rw [show (∏ k, exp (c k * mono σ (supp k))) = ∏ k, (sinh (c k) * mono σ (supp k) + cosh (c k)) from
    Finset.prod_congr rfl (fun k _ => by rw [exp_mul_sign _ _ (mono_eq σ _)]; ring)]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  ring

/-- **Griffiths' first inequality** (for any monomial and non-negative couplings). -/
theorem gks1 {c : κ → ℝ} (hc : ∀ k, 0 ≤ c k) (B : Multiset ι) : 0 ≤ num supp c B := by
  unfold num
  simp_rw [exp_energy_expand supp c, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg (fun S _ => ?_)
  have h : ∀ σ : ι → Bool, mono σ B * ((∏ k ∈ univ \ S, cosh (c k)) * ∏ k ∈ S, (sinh (c k) * mono σ (supp k)))
      = ((∏ k ∈ univ \ S, cosh (c k)) * ∏ k ∈ S, sinh (c k)) * mono σ (B + ∑ k ∈ S, supp k) := by
    intro σ
    rw [mono_add, mono_sum, Finset.prod_mul_distrib]; ring
  simp_rw [h]
  rw [← Finset.mul_sum]
  refine mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun k _ => (cosh_pos _).le))
    (Finset.prod_nonneg (fun k _ => sinh_nonneg_iff.mpr (hc k)))) (sum_mono_nonneg _)

end Model

/-! ## Two replicas -/

section Replica

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (supp : κ → Multiset ι)

/-- Reindex the second replica by `τ = σ ρ` (coordinatewise exclusive or). -/
theorem sum_replica (F : (ι → Bool) → (ι → Bool) → ℝ) :
    ∑ σ : ι → Bool, ∑ τ : ι → Bool, F σ τ = ∑ σ : ι → Bool, ∑ ρ : ι → Bool, F σ (fun i => xor (σ i) (ρ i)) := by
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  refine Fintype.sum_equiv
    (Function.Involutive.toPerm (fun ρ : ι → Bool => fun i => xor (σ i) (ρ i)) (fun ρ => by ext i; simp)) _ _ ?_ |>.symm
  intro ρ; rfl

theorem energy_xor (K J : κ → ℝ) (σ ρ : ι → Bool) :
    energy supp K σ + energy supp J (fun i => xor (σ i) (ρ i)) =
      ∑ k, mono σ (supp k) * (K k + J k * mono ρ (supp k)) := by
  unfold energy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mono_xor]; ring

/-- The two-replica sum behind Ginibre's inequality, for either sign. -/
theorem ginibre_pair {K J : κ → ℝ} (hJK : ∀ k, |J k| ≤ K k) (B : Multiset ι) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    0 ≤ ∑ σ : ι → Bool, ∑ τ : ι → Bool, (mono σ B + s * mono τ B) * exp (energy supp K σ + energy supp J τ) := by
  rw [sum_replica, Finset.sum_comm]
  refine Finset.sum_nonneg (fun ρ _ => ?_)
  have h : ∀ σ : ι → Bool,
      (mono σ B + s * mono (fun i => xor (σ i) (ρ i)) B) *
        exp (energy supp K σ + energy supp J (fun i => xor (σ i) (ρ i))) =
      (1 + s * mono ρ B) * (mono σ B * exp (energy supp (fun k => K k + J k * mono ρ (supp k)) σ)) := by
    intro σ
    rw [energy_xor, mono_xor]
    have : energy supp (fun k => K k + J k * mono ρ (supp k)) σ = ∑ k, mono σ (supp k) * (K k + J k * mono ρ (supp k)) := by
      unfold energy; exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [this]; ring
  simp_rw [h]
  rw [← Finset.mul_sum]
  have hρ : 0 ≤ 1 + s * mono ρ B := by
    rcases hs with rfl | rfl <;> rcases mono_eq ρ B with h1 | h1 <;> rw [h1] <;> norm_num
  refine mul_nonneg hρ (gks1 supp (fun k => ?_) B)
  have h1 := abs_le.mp (hJK k)
  rcases mono_eq ρ (supp k) with h2 | h2 <;> rw [h2] <;> linarith [h1.1, h1.2]

end Replica


/-! ## The inequalities -/

section Main

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (supp : κ → Multiset ι)

theorem pair_expand (K J : κ → ℝ) (B : Multiset ι) (s : ℝ) :
    ∑ σ : ι → Bool, ∑ τ : ι → Bool, (mono σ B + s * mono τ B) * exp (energy supp K σ + energy supp J τ) =
      num supp K B * Zf supp J + s * (Zf supp K * num supp J B) := by
  have e1 : ∑ σ : ι → Bool, ∑ τ : ι → Bool, mono σ B * exp (energy supp K σ + energy supp J τ) =
      num supp K B * Zf supp J := by
    rw [num, Zf, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun τ _ => ?_))
    rw [exp_add]; ring
  have e2 : ∑ σ : ι → Bool, ∑ τ : ι → Bool, mono τ B * exp (energy supp K σ + energy supp J τ) =
      Zf supp K * num supp J B := by
    rw [num, Zf, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun τ _ => ?_))
    rw [exp_add]; ring
  rw [← e1, ← e2, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun τ _ => by ring)

/-- **Ginibre's inequality** (Ginibre 1970), in the form `|J_k| ≤ K_k` for every interaction `k`:
`⟨σ_B⟩_J ≤ ⟨σ_B⟩_K` and `-⟨σ_B⟩_J ≤ ⟨σ_B⟩_K`. -/
theorem ginibre {K J : κ → ℝ} (hJK : ∀ k, |J k| ≤ K k) (B : Multiset ι) :
    corr supp J B ≤ corr supp K B ∧ -corr supp J B ≤ corr supp K B := by
  have hZJ := Zf_pos supp J
  have hZK := Zf_pos supp K
  have hm := ginibre_pair supp hJK B (-1) (Or.inr rfl)
  have hp := ginibre_pair supp hJK B 1 (Or.inl rfl)
  rw [pair_expand] at hm hp
  unfold corr
  constructor
  · rw [div_le_div_iff₀ hZJ hZK]; nlinarith
  · have : -(num supp J B / Zf supp J) = (-num supp J B) / Zf supp J := by ring
    rw [this, div_le_div_iff₀ hZJ hZK]; nlinarith

/-- `|⟨σ_B⟩_J| ≤ ⟨σ_B⟩_{|J|}` for couplings of any sign: the absolute-value bound used in the centre comparison. -/
theorem abs_corr_le_abs (J : κ → ℝ) (B : Multiset ι) : |corr supp J B| ≤ corr supp (fun k => |J k|) B := by
  have h := ginibre supp (K := fun k => |J k|) (J := J) (fun k => le_rfl) B
  exact abs_le.mpr ⟨by linarith [h.2], h.1⟩

/-- `|⟨σ_B⟩_J| ≤ ⟨σ_B⟩_K` whenever `|J| ≤ K`. -/
theorem abs_corr_le {K J : κ → ℝ} (hJK : ∀ k, |J k| ≤ K k) (B : Multiset ι) :
    |corr supp J B| ≤ corr supp K B := by
  have h := ginibre supp hJK B
  exact abs_le.mpr ⟨by linarith [h.2], h.1⟩

/-- **Monotonicity in the couplings (Griffiths II, derivative form, here without differentiation):** for ferromagnetic
couplings `0 ≤ J ≤ K`, `⟨σ_B⟩_J ≤ ⟨σ_B⟩_K`. -/
theorem corr_mono {K J : κ → ℝ} (h0 : ∀ k, 0 ≤ J k) (hJK : ∀ k, J k ≤ K k) (B : Multiset ι) :
    corr supp J B ≤ corr supp K B :=
  (ginibre supp (fun k => by rw [abs_of_nonneg (h0 k)]; exact hJK k) B).1

theorem corr_nonneg {c : κ → ℝ} (hc : ∀ k, 0 ≤ c k) (B : Multiset ι) : 0 ≤ corr supp c B :=
  div_nonneg (gks1 supp hc B) (Zf_pos supp c).le

/-- **Griffiths' second inequality:** `⟨σ_A⟩ ⟨σ_B⟩ ≤ ⟨σ_A σ_B⟩` for non-negative couplings. -/
theorem griffiths2 {c : κ → ℝ} (hc : ∀ k, 0 ≤ c k) (A B : Multiset ι) :
    corr supp c A * corr supp c B ≤ corr supp c (A + B) := by
  have hZ := Zf_pos supp c
  have key : 0 ≤ ∑ σ : ι → Bool, ∑ τ : ι → Bool,
      (mono σ A - mono τ A) * (mono σ B - mono τ B) * exp (energy supp c σ + energy supp c τ) := by
    rw [sum_replica, Finset.sum_comm]
    refine Finset.sum_nonneg (fun ρ _ => ?_)
    have h : ∀ σ : ι → Bool,
        (mono σ A - mono (fun i => xor (σ i) (ρ i)) A) * (mono σ B - mono (fun i => xor (σ i) (ρ i)) B) *
          exp (energy supp c σ + energy supp c (fun i => xor (σ i) (ρ i))) =
        ((1 - mono ρ A) * (1 - mono ρ B)) *
          (mono σ (A + B) * exp (energy supp (fun k => c k + c k * mono ρ (supp k)) σ)) := by
      intro σ
      rw [energy_xor, mono_xor, mono_xor, mono_add]
      have : energy supp (fun k => c k + c k * mono ρ (supp k)) σ =
          ∑ k, mono σ (supp k) * (c k + c k * mono ρ (supp k)) := by
        unfold energy; exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [this]; ring
    simp_rw [h]
    rw [← Finset.mul_sum]
    have h1 : ∀ m : Multiset ι, 0 ≤ 1 - mono ρ m := fun m => by
      rcases mono_eq ρ m with h | h <;> rw [h] <;> norm_num
    refine mul_nonneg (mul_nonneg (h1 A) (h1 B)) (gks1 supp (fun k => ?_) (A + B))
    rcases mono_eq ρ (supp k) with h2 | h2 <;> rw [h2] <;> linarith [hc k]
  have expand : ∑ σ : ι → Bool, ∑ τ : ι → Bool,
      (mono σ A - mono τ A) * (mono σ B - mono τ B) * exp (energy supp c σ + energy supp c τ) =
      2 * (num supp c (A + B) * Zf supp c - num supp c A * num supp c B) := by
    have t : ∀ (f g : (ι → Bool) → ℝ), ∑ σ : ι → Bool, ∑ τ : ι → Bool, f σ * g τ =
        (∑ σ, f σ) * (∑ τ, g τ) := fun f g => (Finset.sum_mul_sum _ _ _ _).symm
    have e : ∀ σ τ : ι → Bool,
        (mono σ A - mono τ A) * (mono σ B - mono τ B) * exp (energy supp c σ + energy supp c τ) =
        (mono σ (A + B) * exp (energy supp c σ)) * exp (energy supp c τ)
        + exp (energy supp c σ) * (mono τ (A + B) * exp (energy supp c τ))
        - (mono σ A * exp (energy supp c σ)) * (mono τ B * exp (energy supp c τ))
        - (mono σ B * exp (energy supp c σ)) * (mono τ A * exp (energy supp c τ)) := by
      intro σ τ; rw [mono_add, mono_add, exp_add]; ring
    simp_rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [t, t, t, t]
    have : ∑ σ : ι → Bool, mono σ (A + B) * exp (energy supp c σ) = num supp c (A + B) := rfl
    simp only [num, Zf]
    ring
  rw [expand] at key
  unfold corr
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hZ hZ) hZ]
  nlinarith [key, hZ]

end Main

end ProofPhase.Centre
