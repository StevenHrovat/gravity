/-
Round-4 preparation, DMP scout (2026-11-21). Released under Apache 2.0.

# The act identity read on a box: the act number z = E · L

Note: `docs/mass-gap/weak-coupling/round4-prep/DMP-SCOUT.md`, section 2.

DMP side (`evidence/Dmp/Reach.lean`, restated here over the reals since `evidence/` is a separate Lean project): an act's existence
`x` times its extent `e` is one quantum `Q` (the act identity, `x · e = Q · k²` in grid units); the witnesses' reach bounds the extent
(`e ≤ R`); then `x ≥ Q / R` on every grid (`mg_reach_existence_floor`).

Yang–Mills side (DMP-SCOUT §2): in a periodic box of side `L`, `x` is the energy `E` of the lowest state with one unit of centre
(electric) flux and `e` is the length `L` the flux has to span; the dimensionless **act number** `z(L) = E(L) · L` (units ħ = c = 1)
is the box's coupling. For free light `z = e²/2 = 2πα` at every `L` (one act spans the box: `single_act_frozen`, `coulomb_frozen`).

What is proved (toys, real arithmetic; no Yang–Mills content):
1. `act_piece_floor`, `act_chain_floor`: a flux of total extent `L` made of acts that each obey the act identity and stay within reach
   `R` has total existence at least `Q · L / R²`: the reach bound turns the act identity into a **string tension** `Q / R²`.
2. `act_number_quadratic`: then `z ≥ Q · L² / R²`: the act number grows like the area (confinement form).
3. `single_act_frozen`: with no reach bound, one act spans the box and `z = Q` at every `L` (the photon: frozen, `mg_no_reach_no_floor`).
4. `coulomb_frozen`, `string_quadruples`, `power_doubling`: under doubling of every length, the Coulomb form keeps `z`, the string form
   multiplies it by 4, a power law `z = C · L^p` multiplies it by `2^p` (semiclassical weak end, `p = 11/3`, heuristic in the note).
5. `act_reach`: if `z` grows by a factor `1 + δ` per doubling while below a target `z*`, every start `z 0 ≥ z₀ > 0` reaches `z*` within
   a number of doublings that depends only on `z₀`, `z*`, `δ` (uniform in the sequence, so in the bare coupling).
6. `nonincreasing_never_reaches`: a non-increasing act number (deconfined Z₂, finite subgroups at large β; frozen U(1)) never reaches
   a target above its start.
7. `boundary_iff_ttl` (3s1t on the box): `z = 1` exactly when the box side equals the flux state's time to live `1/E`: the box where
   space reach and TTL certify the same existence.
-/

import Mathlib

namespace Attempts.R4prep.Act

open Finset

/-- One act within reach: `x · e = Q`, `0 < e ≤ R`, `Q ≥ 0` give `Q · e ≤ x · R²` (the floor `x ≥ Q/R`, weighted by `e/R`). -/
theorem act_piece_floor {Q R x e : ℝ} (hQ : 0 ≤ Q) (he : 0 < e) (hR : e ≤ R) (hact : x * e = Q) :
    Q * e ≤ x * R ^ 2 := by
  have hx0 : 0 ≤ x := by
    by_contra hneg
    push Not at hneg
    have : x * e < 0 := mul_neg_of_neg_of_pos hneg he
    linarith
  calc Q * e = x * (e * e) := by rw [← hact]; ring
    _ ≤ x * (R * R) := mul_le_mul_of_nonneg_left (mul_self_le_mul_self he.le hR) hx0
    _ = x * R ^ 2 := by ring

/-- **A chain of acts within reach.** A flux made of acts `i ∈ s`, each obeying the act identity and within reach `R`, has total
existence at least `Q · (total extent) / R²`. -/
theorem act_chain_floor {ι : Type*} (s : Finset ι) {Q R : ℝ} (x e : ι → ℝ) (hQ : 0 ≤ Q)
    (he : ∀ i ∈ s, 0 < e i) (hR : ∀ i ∈ s, e i ≤ R) (hact : ∀ i ∈ s, x i * e i = Q) :
    Q * (∑ i ∈ s, e i) ≤ (∑ i ∈ s, x i) * R ^ 2 := by
  rw [mul_sum, sum_mul]
  exact sum_le_sum fun i hi => act_piece_floor hQ (he i hi) (hR i hi) (hact i hi)

/-- **The act number grows like the area.** If the acts span the box (`∑ e = L`), the act number `z = L · ∑ x` satisfies
`Q · L² ≤ z · R²`. -/
theorem act_number_quadratic {ι : Type*} (s : Finset ι) {Q R L : ℝ} (x e : ι → ℝ) (hQ : 0 ≤ Q) (hL0 : 0 ≤ L)
    (he : ∀ i ∈ s, 0 < e i) (hR : ∀ i ∈ s, e i ≤ R) (hact : ∀ i ∈ s, x i * e i = Q) (hL : ∑ i ∈ s, e i = L) :
    Q * L ^ 2 ≤ (L * ∑ i ∈ s, x i) * R ^ 2 := by
  have h := act_chain_floor s x e hQ he hR hact
  rw [hL] at h
  calc Q * L ^ 2 = L * (Q * L) := by ring
    _ ≤ L * ((∑ i ∈ s, x i) * R ^ 2) := mul_le_mul_of_nonneg_left h hL0
    _ = (L * ∑ i ∈ s, x i) * R ^ 2 := by ring

/-- **No reach bound: one act spans the box, and the act number is the quantum at every size** (the photon's case). -/
theorem single_act_frozen {Q L x : ℝ} (hact : x * L = Q) : L * x = Q := by
  rw [mul_comm]; exact hact

/-- Coulomb form `E(L⊥, L∥) = c · L∥ / L⊥²`: the act number of the cube is `c` at every side (marginal under doubling). -/
theorem coulomb_frozen (c L : ℝ) (hL : L ≠ 0) : L * (c * L / L ^ 2) = c := by
  field_simp

/-- String form `E = σ · L∥`: doubling every length multiplies the act number by 4. -/
theorem string_quadruples (σ L : ℝ) : (2 * L) * (σ * (2 * L)) = 4 * (L * (σ * L)) := by ring

/-- Power law `z(L) = C · L^p` (the semiclassical weak end): doubling multiplies `z` by `2^p`, more than 1 exactly when `p > 0`. -/
theorem power_doubling (C p L : ℝ) (hL : 0 ≤ L) : C * (2 * L) ^ p = 2 ^ p * (C * L ^ p) := by
  rw [Real.mul_rpow (by norm_num) hL]; ring

theorem power_doubling_gt_one {p : ℝ} (hp : 0 < p) : 1 < (2 : ℝ) ^ p :=
  Real.one_lt_rpow (by norm_num) hp

/-- **Uniform reach from a multiplicative margin.** If the act number grows by at least the factor `1 + δ` per doubling while it is
below `z*`, there is one `N`, depending only on `z₀`, `z*` and `δ`, such that every sequence starting at `z 0 ≥ z₀` reaches `z*`
within `N` doublings. -/
theorem act_reach {z0 zs δ : ℝ} (hδ : 0 < δ) (hz0 : 0 < z0) :
    ∃ N : ℕ, ∀ z : ℕ → ℝ, z0 ≤ z 0 → (∀ j, z j < zs → (1 + δ) * z j ≤ z (j + 1)) → ∃ j ≤ N, zs ≤ z j := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (zs / z0) (by linarith : (1 : ℝ) < 1 + δ)
  refine ⟨N, fun z h0 hstep => ?_⟩
  by_contra hcon
  push Not at hcon
  have key : ∀ j, j ≤ N → (1 + δ) ^ j * z0 ≤ z j := by
    intro j
    induction j with
    | zero => intro _; simpa using h0
    | succ k ih =>
      intro hk
      have hk' : k ≤ N := Nat.le_of_succ_le hk
      have hz := ih hk'
      have hs := hstep k (hcon k hk')
      have hpos : 0 ≤ 1 + δ := by linarith
      calc (1 + δ) ^ (k + 1) * z0 = (1 + δ) * ((1 + δ) ^ k * z0) := by ring
        _ ≤ (1 + δ) * z k := mul_le_mul_of_nonneg_left hz hpos
        _ ≤ z (k + 1) := hs
  have h1 := key N le_rfl
  have h2 := hcon N le_rfl
  have h3 : zs < (1 + δ) ^ N * z0 := (div_lt_iff₀ hz0).mp hN
  linarith

/-- **A non-increasing act number never reaches a target above its start** (deconfined Z₂ and the finite subgroups at large β, where
the flux splitting shrinks with the box; frozen U(1) as the equality case). -/
theorem nonincreasing_never_reaches {z : ℕ → ℝ} {zs : ℝ} (h0 : z 0 < zs) (hmono : ∀ j, z (j + 1) ≤ z j) :
    ∀ j, z j < zs := by
  intro j
  induction j with
  | zero => exact h0
  | succ k ih => exact lt_of_le_of_lt (hmono k) ih

/-- **3s1t on the box.** For a positive flux energy `E`, the act number `L · E` is one exactly when the box side equals the flux
state's time to live `1/E`. -/
theorem boundary_iff_ttl {L E : ℝ} (hE : E ≠ 0) : L * E = 1 ↔ L = E⁻¹ := by
  constructor
  · intro h; exact eq_inv_of_mul_eq_one_left h
  · intro h; rw [h]; exact inv_mul_cancel₀ hE

end Attempts.R4prep.Act
