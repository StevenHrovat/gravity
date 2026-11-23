/-
Proof phase, crossover workstream (c9a-crossover): the hand-over between the sheet-cost (rarity) and the electric (disorder)
mechanisms has a uniform per-box rate at 't Hooft's self-dual point (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/RATE.md`, section 4.
-/

import ProofPhase.Flip.Strict
import ProofPhase.Flip.Floor

/-!
# At every box size, the twist or the electric free energy is at least `log(1 + √2)`

`twistF Z Ztw = −log(Z_tw/Z)` is the free energy of one forced centre sheet through the periodic box (the integer-flux cost,
annealed over everything); `elecF Z Ztw = −log((Z − Z_tw)/(Z + Z_tw))` is the electric-flux free energy, the per-box decay of
a centre-charged signal (`ProofPhase.Flip.Floor`, section 1; `F_e = dual(F_tw)`, `elecF_eq_dual`). The dual is a decreasing
involution with fixed point `log(1 + √2)` (ratio `√2 − 1`).

* **`handover_ratio`** (S): if `0 < Z_tw < Z`, then `Z_tw/Z ≤ √2 − 1` or `(Z − Z_tw)/(Z + Z_tw) < √2 − 1`.
* **`log_one_add_sqrt_two_le_max`** (S): if `0 < Z_tw < Z`, then `log(1 + √2) ≤ max(F_tw, F_e)`.
* **`su2_handover`** (S, with one stated hypothesis): for the SU(2) Wilson action, every `β ≠ 0`, every `L`, every even `T`,
  every spatial background twist and plane position, with `0 < Z_tw` as hypothesis (true, the integrand is positive; not
  formalised in `ProofPhase.Flip`, which proves `0 ≤ Z_tw`): `log(1 + √2) ≤ max(F_tw, F_e)`, from the strict bound
  `su2_Ztw_lt_Z`.

**Claim level.** Lean. Sharp: at `Z_tw/Z = √2 − 1` both free energies equal `log(1 + √2) ≈ 0.881`. What it does **not** give
(RATE.md 4-5): these are free energies of the whole periodic box (annealed, a twist through the torus), not the influence of an
arbitrary outside on a box (quenched), and one box's rate is not yet a product over `D/L` boxes.
-/

open Real

namespace ProofPhase.Crossover

open ProofPhase.Flip

/-- **The self-dual alternative for the ratios** (S). -/
theorem handover_ratio {Z Ztw : ℝ} (hT : 0 < Ztw) (hlt : Ztw < Z) :
    Ztw / Z ≤ √2 - 1 ∨ (Z - Ztw) / (Z + Ztw) < √2 - 1 := by
  have hZ : 0 < Z := hT.trans hlt
  by_cases h : Ztw / Z ≤ √2 - 1
  · exact Or.inl h
  · right
    have hx : √2 - 1 < Ztw / Z := not_le.1 h
    rw [lt_div_iff₀ hZ] at hx
    rw [div_lt_iff₀ (by linarith)]
    have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h2 := mul_lt_mul_of_pos_left hx (show 0 < √2 by positivity)
    nlinarith [hs, h2]

/-- **At every box, the twist or the electric free energy is at least `log(1 + √2)`** (S). -/
theorem log_one_add_sqrt_two_le_max {Z Ztw : ℝ} (hT : 0 < Ztw) (hlt : Ztw < Z) :
    Real.log (1 + √2) ≤ max (twistF Z Ztw) (elecF Z Ztw) := by
  have hZ : 0 < Z := hT.trans hlt
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv : Real.log (1 + √2) = -Real.log (√2 - 1) := by
    rw [← Real.log_inv]
    congr 1
    exact eq_inv_of_mul_eq_one_left (by linear_combination hs)
  rcases handover_ratio hT hlt with h | h
  · apply le_max_of_le_left
    unfold twistF
    rw [hinv]
    exact neg_le_neg (Real.log_le_log (div_pos hT hZ) h)
  · apply le_max_of_le_right
    unfold elecF
    rw [hinv]
    exact neg_le_neg (Real.log_le_log (div_pos (by linarith) (by linarith)) h.le)

/-- **SU(2): the hand-over rate** (S, with `0 < Z_tw` as hypothesis). -/
theorem su2_handover (L : ℕ) [NeZero L] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L)
    {T : ℕ} [NeZero T] (hT : Even T) (hpos : 0 < su2Ztw L β P c T) :
    Real.log (1 + √2) ≤ max (twistF (su2Z L β P T) (su2Ztw L β P c T)) (elecF (su2Z L β P T) (su2Ztw L β P c T)) :=
  log_one_add_sqrt_two_le_max hpos (su2_Ztw_lt_Z L hβ P c hT)

end ProofPhase.Crossover
