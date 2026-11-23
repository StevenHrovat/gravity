/-
Proof phase, crossover workstream (c9a-crossover): twist saturation at one box size, what our pieces give, and where
bond-moving bounds pay (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/SATURATION.md`.
-/

import ProofPhase.Flip.Floor

/-!
# Twist saturation: a tick-unit floor, the link to the electric free energy, and the cost of an upper decimation

* **`ratio_floor_of_pointwise`** (S): if the twisted weight is at least `c` times the untwisted weight configuration by
  configuration, then `Z_tw/Z ≥ c`. With the twist flipping `N` plaquettes, `c = e^{−2βN}`.
* **`exp_floor_ge_iff`** (S): `θ ≤ e^{−2βN} ↔ 2βN ≤ log(1/θ)` (`0 < θ`): the floor saturates the twist only for
  `β N ≤ ½ log(1/θ)`, a strong-coupling condition in tick units.
* **`twist_ratio_of_elecF`** (S): if `0 < Z_tw < Z` and `F_e ≥ log((1 + θ)/(1 − θ))`, then `Z_tw/Z ≥ θ` (`0 ≤ θ < 1`).
  A large electric free energy forces a saturated twist (the dynamical branch selection, one direction).
* **`jensen_normalization`** (S): for a probability vector `w` and `f ≥ 0` with mean `1`, `Σ w f^ζ ≥ 1` for every `ζ ∈ ℕ`.
  The normalisation `F̂₀ = ∫ f^ζ` of a bond-moving (upper) decimation step is at least `1`, so the upper bound
  `Z ≤ F̂₀^{|Λ'|} Z'` carries a factor that only grows with the number of moved plaquettes.
-/

open Finset

noncomputable section

namespace ProofPhase.Crossover

/-- **Pointwise weight ratio gives a partition-function ratio** (S). -/
theorem ratio_floor_of_pointwise {Ω : Type*} (s : Finset Ω) (w wt : Ω → ℝ) {c : ℝ}
    (hpos : 0 < ∑ ω ∈ s, w ω) (hpt : ∀ ω ∈ s, c * w ω ≤ wt ω) : c ≤ (∑ ω ∈ s, wt ω) / ∑ ω ∈ s, w ω := by
  rw [le_div_iff₀ hpos, Finset.mul_sum]
  exact Finset.sum_le_sum hpt

/-- **When the tick-unit floor saturates the twist** (S). -/
theorem exp_floor_ge_iff {θ : ℝ} (hθ : 0 < θ) (x : ℝ) : θ ≤ Real.exp (-x) ↔ x ≤ Real.log (1 / θ) := by
  rw [Real.log_div (by norm_num) hθ.ne', Real.log_one, zero_sub, ← Real.log_le_iff_le_exp hθ]
  constructor <;> intro h <;> linarith

/-- **A large electric free energy saturates the twist** (S). -/
theorem twist_ratio_of_elecF {Z Ztw θ : ℝ} (hT : 0 < Ztw) (hlt : Ztw < Z) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hF : Real.log ((1 + θ) / (1 - θ)) ≤ ProofPhase.Flip.elecF Z Ztw) : θ ≤ Ztw / Z := by
  have hZ : 0 < Z := hT.trans hlt
  have hx : 0 < (Z - Ztw) / (Z + Ztw) := div_pos (by linarith) (by linarith)
  have hq : 0 < (1 + θ) / (1 - θ) := div_pos (by linarith) (by linarith)
  unfold ProofPhase.Flip.elecF at hF
  -- -log x ≥ log q  ⟹  x ≤ 1/q
  have h1 : Real.log ((Z - Ztw) / (Z + Ztw)) ≤ Real.log ((1 - θ) / (1 + θ)) := by
    rw [show (1 - θ) / (1 + θ) = ((1 + θ) / (1 - θ))⁻¹ by rw [inv_div], Real.log_inv]
    linarith
  have h2 := (Real.log_le_log_iff hx (div_pos (by linarith) (by linarith))).1 h1
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at h2
  rw [le_div_iff₀ hZ]
  nlinarith

/-- **The normalisation of an upper (bond-moving) decimation step is at least one** (S, Jensen). -/
theorem jensen_normalization {ι : Type*} (s : Finset ι) (w f : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) (hf : ∀ i ∈ s, 0 ≤ f i) (hmean : ∑ i ∈ s, w i * f i = 1) (ζ : ℕ) :
    1 ≤ ∑ i ∈ s, w i * f i ^ ζ := by
  have h := (convexOn_pow ζ).map_sum_le hw hw1 (fun i hi => Set.mem_Ici.2 (hf i hi))
  simp only [smul_eq_mul] at h
  rw [hmean, one_pow] at h
  exact h

end ProofPhase.Crossover
