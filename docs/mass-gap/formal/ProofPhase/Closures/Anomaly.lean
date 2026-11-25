/-
Closures round (2026-11-24): anomaly cancellation fixes the hypercharge ratios of one Standard Model generation, and
with them the Z_6 of `General/GUCentre.lean`. Released under Apache 2.0.

Paper: Part IX, IX.4.1 and IX.7 item 2 (claim IX.7b); `docs/paper/OPEN-CLAIMS-CLOSURES.md`.
-/

import ProofPhase.General.GUCentre

/-!
# Anomaly cancellation fixes the hypercharges, hence the Z_6

**Classical** (Geng and Marshak 1989; Minahan, Ramond and Warner 1990; Babu and Mohapatra 1989), formalised here. Nothing
in this file is new physics.

**Set-up.** One generation of Standard Model fermions, in the convention of `smFields` (`Q = T_3 + Y`, right-handed
singlets): `Q_L (3,2)`, `u_R (3,1)`, `d_R (3,1)`, `L_L (1,2)`, `e_R (1,1)`, with unknown hypercharges `Y = q/6`, `q` an
integer (`Gen`). A right-handed field enters the anomaly sums with a minus sign. The four conditions (`AnomalyFree`):

* `SU(3)^2 U(1)`:  `2 q_Q - q_u - q_d = 0`;
* `SU(2)^2 U(1)`:  `3 q_Q + q_L = 0`;
* gravitational `U(1)`:  `6 q_Q - 3 q_u - 3 q_d + 2 q_L - q_e = 0`;
* `U(1)^3`:  `6 q_Q^3 - 3 q_u^3 - 3 q_d^3 + 2 q_L^3 - q_e^3 = 0`.

**The theorems.**
* `anomalyFree_iff` (S): the solutions are exactly `q = q_Q (1, 4, -2, -3, -6)` (or the same with `u` and `d`
  exchanged), or the degenerate family `q_Q = q_L = q_e = 0`, `q_d = -q_u`.
* `anomaly_fixes_sm` (S): with `q_Q > 0` and the charges coprime (the U(1) normalised so that the generation's charges
  have no common factor), the charges are those of `smFields`: `(1, 4, -2, -3, -6)`, up to the label swap `u <-> d`.
* `anomaly_fixes_Z6` (S): under the same hypotheses, the centre elements of `SU(3) x SU(2) x U(1)` acting trivially on the
  generation are exactly `(z^2, z^3, z)` with `z^6 = 1`, a cyclic group of order 6 (`sm_kernel`), and the generator
  `(zeta6^2, zeta6^3, zeta6)` acts trivially on every field (`gen_trivial_iff`).

**What is assumed, and stated.** The representation content of one generation is the input (it is what the anomaly
equations are about). The degenerate family (`q_Q = 0`) solves the four equations; it is excluded by the hypothesis
`0 < q_Q` (classically by the Yukawa couplings, which need a hypercharge on the quark doublet). The Higgs is a scalar and
does not enter the anomaly sums; its charge is fixed by the Yukawa couplings and is not used here (the Z_6 is already
fixed by the fermions).
-/

namespace ProofPhase.Closures.Anomaly

open ProofPhase.General.GU

/-- The hypercharges of one generation, times six: `Q_L`, `u_R`, `d_R`, `L_L`, `e_R`. -/
structure Gen where
  Q : ℤ
  u : ℤ
  d : ℤ
  L : ℤ
  e : ℤ

/-- **Anomaly cancellation** for one generation (right-handed fields with a minus sign). -/
structure AnomalyFree (g : Gen) : Prop where
  su3 : 2 * g.Q - g.u - g.d = 0
  su2 : 3 * g.Q + g.L = 0
  grav : 6 * g.Q - 3 * g.u - 3 * g.d + 2 * g.L - g.e = 0
  cubic : 6 * g.Q ^ 3 - 3 * g.u ^ 3 - 3 * g.d ^ 3 + 2 * g.L ^ 3 - g.e ^ 3 = 0

/-- The Standard Model values satisfy the four conditions. -/
theorem anomalyFree_sm : AnomalyFree ⟨1, 4, -2, -3, -6⟩ :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Equality of generations, field by field. -/
theorem gen_eq_iff (g : Gen) (Q u d L e : ℤ) :
    g = ⟨Q, u, d, L, e⟩ ↔ g.Q = Q ∧ g.u = u ∧ g.d = d ∧ g.L = L ∧ g.e = e := by
  cases g; simp

/-- **The solutions of the anomaly equations** (S): the Standard Model ratios (up to the swap `u <-> d`), or the
degenerate family with `q_Q = 0`. -/
theorem anomalyFree_iff (g : Gen) :
    AnomalyFree g ↔
      (g.L = -3 * g.Q ∧ g.e = -6 * g.Q ∧
        ((g.u = 4 * g.Q ∧ g.d = -2 * g.Q) ∨ (g.u = -2 * g.Q ∧ g.d = 4 * g.Q))) ∨
      (g.Q = 0 ∧ g.L = 0 ∧ g.e = 0 ∧ g.d = -g.u) := by
  constructor
  · rintro ⟨h3, h2, hg, hc⟩
    have hL : g.L = -3 * g.Q := by linarith
    have hd : g.d = 2 * g.Q - g.u := by linarith
    have he : g.e = -6 * g.Q := by linarith
    have h18 : 18 * (g.Q * ((g.u - 4 * g.Q) * (g.u + 2 * g.Q))) = 0 := by
      rw [hL, hd, he] at hc
      linear_combination (-1 : ℤ) * hc
    have hQ : g.Q * ((g.u - 4 * g.Q) * (g.u + 2 * g.Q)) = 0 := by
      rcases mul_eq_zero.1 h18 with h | h
      · norm_num at h
      · exact h
    rcases mul_eq_zero.1 hQ with h0 | h1
    · right
      exact ⟨h0, by rw [hL, h0]; ring, by rw [he, h0]; ring, by rw [hd, h0]; ring⟩
    · left
      refine ⟨hL, he, ?_⟩
      rcases mul_eq_zero.1 h1 with h | h
      · left; constructor <;> linarith
      · right; constructor <;> linarith
  · rintro (⟨hL, he, (⟨hu, hd⟩ | ⟨hu, hd⟩)⟩ | ⟨hQ, hL, he, hd⟩)
    · exact ⟨by rw [hu, hd]; ring, by rw [hL]; ring, by rw [hu, hd, hL, he]; ring,
        by rw [hu, hd, hL, he]; ring⟩
    · exact ⟨by rw [hu, hd]; ring, by rw [hL]; ring, by rw [hu, hd, hL, he]; ring,
        by rw [hu, hd, hL, he]; ring⟩
    · exact ⟨by rw [hd, hQ]; ring, by rw [hL, hQ]; ring, by rw [hd, hQ, hL, he]; ring,
        by rw [hd, hQ, hL, he]; ring⟩

/-- The charges have no common factor: every common divisor is a unit (the U(1) normalised on the generation). -/
def Primitive (g : Gen) : Prop :=
  ∀ k : ℤ, k ∣ g.Q → k ∣ g.u → k ∣ g.d → k ∣ g.L → k ∣ g.e → IsUnit k

/-- **Anomaly cancellation fixes the Standard Model charges** (S): with `q_Q > 0` and coprime charges, the generation is
`(1, 4, -2, -3, -6)`, or the same with `u` and `d` exchanged. -/
theorem anomaly_fixes_sm (g : Gen) (hA : AnomalyFree g) (hQ : 0 < g.Q) (hP : Primitive g) :
    g = ⟨1, 4, -2, -3, -6⟩ ∨ g = ⟨1, -2, 4, -3, -6⟩ := by
  rcases (anomalyFree_iff g).1 hA with ⟨hL, he, huD⟩ | ⟨h0, -, -, -⟩
  · have hdivL : g.Q ∣ g.L := ⟨-3, by rw [hL]; ring⟩
    have hdivE : g.Q ∣ g.e := ⟨-6, by rw [he]; ring⟩
    have hdivU : g.Q ∣ g.u := by
      rcases huD with ⟨hu, -⟩ | ⟨hu, -⟩
      · exact ⟨4, by rw [hu]; ring⟩
      · exact ⟨-2, by rw [hu]; ring⟩
    have hdivD : g.Q ∣ g.d := by
      rcases huD with ⟨-, hd⟩ | ⟨-, hd⟩
      · exact ⟨-2, by rw [hd]; ring⟩
      · exact ⟨4, by rw [hd]; ring⟩
    have hU : IsUnit g.Q := hP g.Q dvd_rfl hdivU hdivD hdivL hdivE
    have h1 : g.Q = 1 := by
      rcases Int.isUnit_iff.1 hU with h | h
      · exact h
      · omega
    rcases huD with ⟨hu, hd⟩ | ⟨hu, hd⟩
    · left
      rw [gen_eq_iff]
      refine ⟨h1, ?_, ?_, ?_, ?_⟩ <;> omega
    · right
      rw [gen_eq_iff]
      refine ⟨h1, ?_, ?_, ?_, ?_⟩ <;> omega
  · omega

/-- The five fermion fields of a generation, as centre data (triality, duality, `q = 6 Y`). -/
def fields (g : Gen) : List SMField :=
  [⟨1, 1, g.Q⟩, ⟨1, 0, g.u⟩, ⟨1, 0, g.d⟩, ⟨0, 1, g.L⟩, ⟨0, 0, g.e⟩]

/-- The Standard Model fermions (the first five entries of `smFields`). -/
def smFermions : List SMField := [⟨1, 1, 1⟩, ⟨1, 0, 4⟩, ⟨1, 0, -2⟩, ⟨0, 1, -3⟩, ⟨0, 0, -6⟩]

theorem smFermions_sub : ∀ f ∈ smFermions, f ∈ smFields := by
  intro f hf
  simp only [smFermions, List.mem_cons, List.not_mem_nil, or_false] at hf
  simp only [smFields, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- **The kernel on the fermions alone** (S): a centre element acts trivially on the five fermions iff it is
`(z^2, z^3, z)` with `z^6 = 1`. -/
theorem fermion_kernel (u v z : ℂ) (hz : z ≠ 0) :
    (∀ f ∈ smFermions, centrePhase u v z f = 1) ↔ z ^ 6 = 1 ∧ u = z ^ 2 ∧ v = z ^ 3 := by
  have h2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have h3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz
  constructor
  · intro h
    have hQ := h ⟨1, 0, -2⟩ (by simp [smFermions])
    have hL := h ⟨0, 1, -3⟩ (by simp [smFermions])
    have hE := h ⟨0, 0, -6⟩ (by simp [smFermions])
    simp only [centrePhase, pow_zero, pow_one, one_mul, mul_one, _root_.zpow_neg, zpow_ofNat] at hQ hL hE
    have hQ' : u * (z ^ 2)⁻¹ = 1 := by simpa using hQ
    have hL' : v * (z ^ 3)⁻¹ = 1 := by simpa using hL
    have hE' : (z ^ 6)⁻¹ = 1 := by simpa using hE
    exact ⟨inv_eq_one.mp hE', (mul_inv_eq_one₀ h2).mp hQ', (mul_inv_eq_one₀ h3).mp hL'⟩
  · intro hk f hf
    exact (sm_kernel u v z hz).2 hk f (smFermions_sub f hf)

/-- The fields of the two Standard Model solutions are the Standard Model fermions (as a set). -/
theorem mem_fields_sm {g : Gen} (hg : g = ⟨1, 4, -2, -3, -6⟩ ∨ g = ⟨1, -2, 4, -3, -6⟩) (f : SMField) :
    f ∈ fields g ↔ f ∈ smFermions := by
  rcases hg with rfl | rfl
  · simp only [fields, smFermions]
  · simp only [fields, smFermions, List.mem_cons, List.not_mem_nil, or_false]
    tauto

/-- **Anomaly cancellation fixes the Z_6** (S). For a generation satisfying the four anomaly conditions, with `q_Q > 0`
and coprime charges: the centre elements acting trivially on its fermions are exactly `(z^2, z^3, z)`, `z^6 = 1` (a cyclic
group of order 6, `sm_kernel_cyclic`), and the generator `(zeta6^2, zeta6^3, zeta6)` acts trivially on each field. -/
theorem anomaly_fixes_Z6 (g : Gen) (hA : AnomalyFree g) (hQ : 0 < g.Q) (hP : Primitive g) :
    (∀ u v z : ℂ, z ≠ 0 → ((∀ f ∈ fields g, centrePhase u v z f = 1) ↔ z ^ 6 = 1 ∧ u = z ^ 2 ∧ v = z ^ 3)) ∧
      ∀ f ∈ fields g, centrePhase (zeta6 ^ 2) (zeta6 ^ 3) zeta6 f = 1 := by
  have hg := anomaly_fixes_sm g hA hQ hP
  refine ⟨fun u v z hz => ?_, fun f hf => ?_⟩
  · rw [← fermion_kernel u v z hz]
    exact forall_congr' fun f => imp_congr_left (mem_fields_sm hg f)
  · have hf' := (mem_fields_sm hg f).1 hf
    rw [gen_trivial_iff]
    simp only [smFermions, List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl | rfl | rfl <;> norm_num

end ProofPhase.Closures.Anomaly
